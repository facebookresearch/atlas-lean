# The dynamic pivot (dynamic VCG) mechanism

Consider agents interacting through a finite-horizon Markov decision process with finite states and actions, per-period valuations $v_i(t, s, k)$ and discount factor $\gamma \ge 0$. The dynamic pivot mechanism executes an efficient policy and, in each period, charges agent $i$ the loss its presence imposes on the others' optimal expected continuation welfare. Truthful reporting in every period is a within-period ex-post Nash equilibrium, payments are nonnegative, and the mechanism is individually rational in every period.

## Proof sketch

Agent $i$'s continuation utility under the mechanism equals the total optimal continuation welfare minus the others' optimal welfare without $i$; the latter is independent of $i$'s reports, and the former is maximized by truthful reporting by Bellman optimality.

## Depends on

- [Markov decision process](../../../ComputerScience/heuristic-search-and-planning/value-iteration/mdp.md)
- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)

## Proof depends on

- [VCG with Clarke pivot payments is incentive compatible](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-clarke.md)

## Sources

- Dirk Bergemann and Juuso Valimaki, "The Dynamic Pivot Mechanism", Econometrica, 2010.
- David C. Parkes and Satinder Singh, "An MDP-Based Approach to Online Mechanism Design", Advances in Neural Information Processing Systems 16 (NeurIPS 2003), 2003.
- David C. Parkes, "Online Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
