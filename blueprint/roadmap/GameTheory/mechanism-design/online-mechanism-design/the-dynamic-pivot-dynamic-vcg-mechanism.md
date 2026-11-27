# The dynamic pivot (dynamic VCG) mechanism

Consider agents with private and independent values in a discrete-time, infinite-horizon model with a common discount factor $0 < \delta < 1$. In each period $t$ an allocation $a_t$ is chosen from a finite set $A$; agent $i$ privately observes its own state $\theta_{i,t}$ and receives flow utility $v_i(a_t, \theta_{i,t}) - p_{i,t}$, and its next state is drawn from a kernel $F_i(\cdot\,; \theta_{i,t}, a_t)$. The initial priors and the kernels are common knowledge and independent across agents, and expected absolute flow utilities are bounded. The dynamic pivot mechanism executes the efficient policy on the reported states and, in each period, charges agent $i$ the others' flow utility at the allocation that would be efficient without $i$ minus their flow utility at the efficient allocation, plus $\delta$ times the difference between the others' optimal expected continuation welfare without $i$ after those two allocations. These payments are nonnegative. Truthful reporting is periodic ex post incentive compatible: in every period, whatever the history and the other agents' current states, it is a best response when the others report truthfully. The mechanism also satisfies the periodic ex post participation constraints: after every history each agent's equilibrium payoff is at least that of opting out permanently, after which the efficient policy is run for the remaining agents.

## Proof sketch

Agent $i$'s continuation utility under the mechanism equals the total optimal continuation welfare minus the others' optimal welfare without $i$. Because types and transitions are independent across agents, the latter does not depend on $i$'s reports, and the former is maximized by truthful reporting by Bellman optimality. The continuation utility is $i$'s marginal contribution to the optimal welfare, which is nonnegative, and payments are nonnegative because the others' optimal welfare without $i$ is at least their welfare under the efficient allocation.

## Depends on

- [Markov decision process](../../../ComputerScience/heuristic-search-and-planning/value-iteration/mdp.md)
- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)

## Proof depends on

- [VCG with Clarke pivot payments is incentive compatible](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-clarke.md)

## Sources

- Dirk Bergemann and Juuso Valimaki, "The Dynamic Pivot Mechanism", Econometrica, 2010.
- David C. Parkes and Satinder Singh, "An MDP-Based Approach to Online Mechanism Design", Advances in Neural Information Processing Systems 16 (NeurIPS 2003), 2003.
- David C. Parkes, "Online Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
