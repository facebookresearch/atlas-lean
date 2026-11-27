# Three-state broadcast law and multiset observations

The root state is uniform on three values. For correlation $-1/2\le\lambda\le1$, transmit a state unchanged with probability $(1+2\lambda)/3$ and to each other state with probability $(1-\lambda)/3$. At different child edges these transitions are independent conditional on the parent state. The branching count is either a fixed natural $b$ or an independent Poisson random variable of mean $d$. Observation at depth zero is the state; at depth $h+1$ take the multiset of depth-$h$ observations from the independent children. Thus the observation records the unordered truncated tree and terminal states, not internal states. The reconstruction statistic is the expected total variation of the posterior of the root from its uniform prior: for each observation of positive mass use Bayes' ratio, then weight by the observation's marginal mass. A zero-mass observation contributes zero regardless of the posterior convention.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThreeStateTreeClauses.lean#L11-L85)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThreeStateSupercritical.lean#L7-L96)
