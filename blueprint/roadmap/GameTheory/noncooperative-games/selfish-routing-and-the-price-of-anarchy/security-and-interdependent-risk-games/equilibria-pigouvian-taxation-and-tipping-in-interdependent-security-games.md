# Equilibria, Pigouvian taxation and tipping in interdependent security games

An agent invests in a best response iff $c_i \le p_i L_i \cdot \Pr[\text{no contagion reaches } i]$, so the incentive to invest decreases as fewer peers invest; iterating best responses from the all-unprotected profile converges to a pure Nash equilibrium, and pure equilibria always exist. In symmetric games with cost $c$, direct-loss probability $p$ and loss $L$, both all-invest and none-invest are equilibria iff $p L\, \pi_{n-1} \le c \le p L$, where $\pi_k$ is the probability that no contagion reaches an agent when exactly $k$ others do not invest; as the number of agents grows, with fixed $c > 0$ and positive transmission probability, investing eventually ceases to be a dominant strategy; and any tax $\tau > c$ on non-investment makes investing strictly dominant, so all-invest is the unique (coarse correlated) equilibrium. If a coalition $K$ is such that, while the agents of $K$ invest, investing is a best response for every agent outside $K$ (a tipping coalition), then, with $K$ held at investing, the best responses of the other agents lead to all-invest; all-invest is then a Nash equilibrium if and only if $c_i \le p_i L_i$ for every $i \in K$.

## Proof sketch

The investment gain is the direct risk discounted by the probability that contagion strikes anyway, which is monotone in the set of unprotected peers; this strategic complementarity gives monotone best-response dynamics, and the geometric sums for symmetric agents give the large-population limit.

## Depends on

- [Interdependent security game](interdependent-security-game.md)
- [Coarse correlated equilibrium](../../no-regret-dynamics/is-coarse-correlated-eq.md)

## Sources

- Howard Kunreuther and Geoffrey Heal, "Interdependent Security", Journal of Risk and Uncertainty, 2003.
- Geoffrey Heal and Howard Kunreuther, "Modeling Interdependent Risks", Risk Analysis, 2007.
