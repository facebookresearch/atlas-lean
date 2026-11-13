# Valid HMMs

For finite sets $S$ of states and $O$ of observations, the valid HMMs are the
HMMs with states $S$, observations $O$ and real weights whose initial weights are positive and sum
to $1$, whose transition weights out of each state are positive and sum to $1$, and whose emission
weights from each state are positive and sum to $1$. They form the parameter space of
Baum-Welch.
