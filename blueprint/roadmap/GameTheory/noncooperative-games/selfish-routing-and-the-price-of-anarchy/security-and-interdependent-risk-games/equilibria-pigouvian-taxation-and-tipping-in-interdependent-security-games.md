# Equilibria, Pigouvian taxation and tipping in interdependent security games

An agent invests in a best response iff $c_i \le p_i L_i \cdot \Pr[\text{no contagion reaches } i]$, so the incentive to invest decreases as fewer peers invest; iterating best responses from the all-unprotected profile converges to a pure Nash equilibrium, and pure equilibria always exist. In symmetric games, both all-invest and none-invest may be equilibria, the coexistence condition is explicit, and as the number of agents grows investing eventually ceases to be a dominant strategy; a suitable tax on non-investment makes all-invest the unique (coarse correlated) equilibrium. If a coalition's investment makes investing a best response for everyone else (a tipping coalition), then all-invest is an equilibrium and best-response cascades reach it; replacing coalition members by agents with higher contagion potential preserves tipping under an alignment of normalized costs.

## Proof sketch

The investment gain is the direct risk discounted by the probability that contagion strikes anyway, which is monotone in the set of unprotected peers; this strategic substitutability gives monotone best-response dynamics, and the geometric sums for symmetric agents give the large-population limit.

## Depends on

- [Interdependent security game](interdependent-security-game.md)
- [Coarse correlated equilibrium](../../no-regret-dynamics/is-coarse-correlated-eq.md)

## Sources

- Howard Kunreuther and Geoffrey Heal, "Interdependent Security", Journal of Risk and Uncertainty, 2003.
- Geoffrey Heal and Howard Kunreuther, "Modeling Interdependent Risks", Risk Analysis, 2007.
