# Equal infima without a Monge optimizer for the three-marginal Coulomb cost

There is a probability density $\rho\ge0$ on $\mathbb R^3$ for which both $\rho$ and its nonnegative square root are smooth and compactly supported, and $\int\rho=1$. Write $\mu=\rho\,dx$. For triples use the extended nonnegative cost $c(x,y,z)=\|x-y\|^{-1}+\|x-z\|^{-1}+\|y-z\|^{-1}$, with inverse zero distance equal to $+\infty$. Let $K$ be the infimum of $\int c\,d\pi$ over probability measures on triples with all three marginals $\mu$. Let $M$ be the corresponding infimum over graph couplings $(\mathrm{id},T_2,T_3)_\#\mu$, where both maps are Borel and preserve $\mu$.

Then $K<\infty$ and a coupling attains it, but every such graph coupling has cost strictly greater than $K$. Nevertheless $M=K$, and for each real $\epsilon>0$ two such maps have finite graph cost at most $K+\epsilon$.

## Depends on

- [Couplings](monge-kantorovich-existence-theorem/couplings.md), extended to three fixed identical marginals.

## Proof depends on

- A smooth marginal construction forcing non-graph optimality, attainment with finite cost, and graph-coupling approximation controlling the collision singularities.

## Expansion

Prove the three-marginal existence and graph-pushforward interfaces, then split the specific density and obstruction from the cost-controlled finite graph approximation. Weak approximation by itself does not give the asserted upper bound for a singular cost.

## Sources

- OpenAI, [CoulombCounterexample comparator, coulomb_counterexample_and_equal_infima](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CoulombCounterexample.lean#L94-L97).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/373.md).
