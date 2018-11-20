import java.util.HashMap;
import java.util.ArrayList;
import negotiator.AgentID;
import java.util.List;
import java.util.Arrays;

import negotiator.bidding.BidDetails;
import negotiator.parties.AbstractNegotiationParty;
import negotiator.session.TimeLineInfo;
import negotiator.actions.Accept;
import negotiator.actions.Reject;
import negotiator.actions.Action;
import negotiator.actions.Offer;
import negotiator.utility.AbstractUtilitySpace;
import negotiator.boaframework.SortedOutcomeSpace;
import negotiator.Bid;
import negotiator.Deadline;
import static java.lang.Math.sqrt;
import static java.lang.Math.pow;
import static java.lang.Math.max;
import static java.lang.Math.min;

//Assumption: Stacking alternate offers protocol

public class Group2 extends AbstractNegotiationParty {

	private boolean criticalSec = false, initialRound = true;
	private double  stepThreshold, timeChange = 0.0, timeThreshold = 0.02;

	private List<BidDetails> outcomeSpace;
	private boolean roundType = false;
	private double discFactor, resValue, dealUtil = 0.95, lastUtil = 0.0;
	private int partyCount, spaceSize, agentId, pIndex = 0;
	private double rounds, pUtil = 1.0;
	private List<Bid> bidSpace = new ArrayList<Bid>();
	private List<Double> selfUtils = new ArrayList<Double>();
	
	private HashMap<String, Integer> agentSeq = new HashMap<String, Integer>();
	private Bid lastBid;

	private double average[], variance[], deviation[], target[], emax[], bidUtils[][];
	private int bidCount[];
	private List<Double> propUtils = new ArrayList<Double>();
	private double gc, lc, alpha = 10, timeFraction = 0.0, presentTime = 0.0, totalTime = 1.0, acceptProb = 0.0;

	private double overallTarget, overallEmax, recordUtil;
	private double delta = 0, timeSplitFactor = 2;
	private boolean deltaflag = false;
	private SortedOutcomeSpace sos;
	private int recordIndex;
	
	@Override
	public void init(AbstractUtilitySpace utilSpace, Deadline dl, TimeLineInfo tl, long randomSeed, AgentID agentId) {
		super.init(utilSpace, dl, tl, randomSeed, agentId);
		if(this.deadlines.getType().toString() == "ROUND") roundType = true;

		sos = new SortedOutcomeSpace(this.utilitySpace);
		outcomeSpace = sos.getAllOutcomes();		
	}

	@Override
	public void receiveMessage(AgentID sender, Action arguments) {

		super.receiveMessage(sender, arguments);
		boolean flag = false;

		resValue = this.utilitySpace.getReservationValueUndiscounted();
		discFactor = this.utilitySpace.getDiscountFactor();
		partyCount = this.getNumberOfParties();
		spaceSize = outcomeSpace.size();
		average = new double[partyCount];
		bidCount = new int[partyCount];
		variance = new double[partyCount];
		deviation = new double[partyCount];
		target = new double[partyCount];
		emax = new double[partyCount];
		bidUtils = new double[partyCount][1000];

		timeSplitFactor = pow(2, 2 - discFactor);

		if(sender != null)
		{
			if(initialRound)
				getAgentIndex(sender);
			if(arguments != null)
				flag = true;
		}
		else {

			

			for (int i = 0; i < outcomeSpace.size(); i++)
			{
				bidSpace.add(outcomeSpace.get(i).getBid());
				selfUtils.add(outcomeSpace.get(i).getMyUndiscountedUtil());
				if(outcomeSpace.get(i).getMyUndiscountedUtil() <= resValue)
					continue;
				propUtils.add(outcomeSpace.get(i).getMyUndiscountedUtil());
			}

			for (int j = 0; j < partyCount; j++) 
			{
				average[j] = 0;
				bidCount[j] = 0;
				variance[j] = 0;
				deviation[j] = 0;
				target[j] = 1.0;
				emax[j] = resValue;
				bidUtils[j][0] = 0;
			}

			rounds = this.deadlines.getValue();
			totalTime = rounds;
			gc = rounds/timeSplitFactor;
			lc = gc;
			if(roundType == true)
				stepThreshold = (Math.sqrt(rounds));
			else stepThreshold = 0.25 * partyCount;
			if (discFactor != 1.0) dealUtil = max(dealUtil, selfUtils.get((int)(selfUtils.size()/2)));	
			else dealUtil = 1.0;
		}

		if(flag)
		{

			try{

				agentId = getAgentIndex(sender);

				///////////////////////

				bidCount[agentId] += 1;

				if(getUtility(Action.getBidFromAction(arguments)) != 0)
				{
					////// do something to calculate time fraction at every message received
					timeFraction = (presentTime * 1.0) / totalTime;

					lastBid = Action.getBidFromAction(arguments);
					lastUtil = getUtility(lastBid);

					if (getUtility(Action.getBidFromAction(arguments)) > resValue) {

						double tempUtil = getUtility(Action.getBidFromAction(arguments));
						int index = bidCount[agentId] - 1;
						bidUtils[agentId][index] = lastUtil;
						double oldAvg = average[agentId];
						average[agentId] = (((oldAvg * index * 1.0) + lastUtil ) / (1.0 * bidCount[agentId]));
						double oldVar = variance[agentId];
						variance[agentId] = (((index * (oldVar + (oldAvg * oldAvg))) + (lastUtil * lastUtil)) / (1.0 * bidCount[agentId])) - (average[agentId] * average[agentId]);
						deviation[agentId] = sqrt(12 * variance[agentId]);
						emax[agentId] = average[agentId] + ((1 - average[agentId]) * deviation[agentId]);
						///// time fraction is being used here
						target[agentId] = 1 - (1 - emax[agentId]) * pow(timeFraction , alpha); 


						overallEmax = 0;
						overallTarget = 0;
						double temp1[], temp2[];
						temp1 = new double[partyCount];
						temp2 = new double[partyCount];
						for (int k = 0; k < partyCount; k++) {

							//overallTarget += target[k];
							//overallEmax += emax[k];

							//temp1[k] = target[k];
							//temp2[k] = emax[k];

							if (overallTarget < target[k]) overallTarget = target[k];
							if (overallEmax < emax[k]) overallEmax = emax[k];
						}

						//Arrays.sort(temp1);
						//Arrays.sort(temp2);

						//overallTarget = max(resValue * 1.5, temp1[(4 * partyCount / 5)]);
						//overallEmax = max(resValue * 1.5, temp2[(4 * partyCount / 5)]);

						//overallTarget /= partyCount;
						//overallEmax /= partyCount;
						overallEmax = max(resValue * 1.75, overallEmax) ;
						overallTarget = max(resValue * 1.75, overallTarget) ;
						if (overallEmax > 1) overallEmax = 1.0;
						if (overallTarget > 1) overallTarget = 1.0;

						acceptProb = ((timeFraction * timeFraction) / 5) + (tempUtil - overallEmax) + (tempUtil - overallTarget);  
					}	
				}

			}
			catch(Exception e) {
				System.out.println("Error");
			}
		}
	}
	
	public int getAgentIndex(AgentID agentId)
	{
		if(agentSeq.containsKey(agentId.toString())) initialRound = false; 
		else agentSeq.put(agentId.toString(), agentSeq.size());
		return agentSeq.get(agentId.toString());
	}
	
	@Override
	public Action chooseAction(List<Class<? extends Action>> possibleActions) {
		int selfIndex = 0;
		if(initialRound) selfIndex = getAgentIndex(this.getPartyId());

		if(!criticalSec)
		{
			if(roundType == false) lc = gc - this.timeline.getCurrentTime() + timeChange;
			else lc--;

			if(lc <= 0)
			{
				if(roundType == false) timeChange = this.timeline.getCurrentTime();
				/*
				if (timeSplitFactor <= 2) gc /= timeSplitFactor;
				else if (timeSplitFactor <= 2.5) gc /= 1.875;
				else if (timeSplitFactor <= 3)	gc /= 1.75;
				else if (timeSplitFactor <= 3.5) gc /= 1.625;
				else if (timeSplitFactor <= 4) gc /= 1.5;
				else gc /= 1.375;
				*/
				gc /= timeSplitFactor;
				lc = gc;
				if(lc < stepThreshold) {
					criticalSec = true;
					recordIndex = pIndex;
					recordUtil = propUtils.get(recordIndex);
					deltaflag = true;
				} 
				pIndex++;
				if(pIndex >= propUtils.size()) pIndex--;
			}
		}

		pUtil = propUtils.get(pIndex);
		if(roundType) {
			rounds--;
			presentTime += 1;
		}
		else {
			rounds = this.timeline.getTotalTime() - this.timeline.getCurrentTime();
			presentTime = this.timeline.getCurrentTime();
		}

		if (roundType == true) {
			if(rounds <= 1 && getAgentIndex(this.getPartyId()) != 0 && lastUtil > resValue)
				return new Accept();
			/*
			else if (rounds <= 1 && getAgentIndex(this.getPartyId()) != 0 && lastUtil <= resValue)
				return new Reject();
			*/
			else if(lastUtil < pUtil && lastUtil < dealUtil)
			{
				if (criticalSec) {
					if (Math.random() <= acceptProb/2) 
						return new Accept();
					else {
						lastBid = generateBid();
						lastUtil = getUtility(lastBid);
						return new Offer(lastBid);
					}
				}
				else {
					lastBid = generateBid();
					lastUtil = getUtility(lastBid);
					return new Offer(lastBid);
				}
			}
			else{
				return new Accept();
			}
		}
		else {
			if(rounds <= timeThreshold && getAgentIndex(this.getPartyId()) != 0 && lastUtil > resValue)
				return new Accept();
			/*
			else if (rounds <= timeThreshold && getAgentIndex(this.getPartyId()) != 0 && lastUtil <= resValue)
				return new Reject();
			*/
			else if(lastUtil < pUtil && lastUtil < dealUtil)
			{
				if (criticalSec) {
					if (Math.random() <= acceptProb/2) 
						return new Accept();
					else {
						lastBid = generateBid();
						lastUtil = getUtility(lastBid);
						return new Offer(lastBid);
					}
				}
				else {
					lastBid = generateBid();
					lastUtil = getUtility(lastBid);
					return new Offer(lastBid);
				}
			}
			else{
				return new Accept();
			}
		}

	}
	
	public Bid generateBid()
	{
		if(criticalSec) 
		{
			double value = min( 1.0 , 
								max ( resValue + 0.1 , 
									  (-0.005 + overallTarget + (Math.random() * 0.01))
									)
							  );
			if (deltaflag == true) {
				delta = max (recordUtil - value, 0);
				deltaflag = false;
			}
			double finalVal =  min ((value + delta), recordUtil * 0.95 );
			
			
			double alternative = getUtility(this.outcomeSpace.get(pIndex).getBid());
			//if (alternative - finalVal > 0.3 ) finalVal = ((alternative/4) + ((3 *finalVal)/4)) ;
			BidDetails bd = this.sos.getBidNearUtility(min(1.0,finalVal)) ;
			return (bd.getBid());
		}
		return this.outcomeSpace.get(pIndex).getBid();
	}

}
