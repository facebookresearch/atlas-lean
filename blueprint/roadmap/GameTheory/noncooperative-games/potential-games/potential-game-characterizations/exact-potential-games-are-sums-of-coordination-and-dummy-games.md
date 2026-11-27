# Exact potential games are sums of coordination and dummy games

A game $G$ with costs $c_i$ admits an exact potential if and only if $c_i = P + d_i$ for a common cost function $P : \prod_j S_j \to \mathbb{R}$ (a coordination game) and functions $d_i$ that do not depend on player $i$'s own strategy (a dummy game).

## Proof sketch

If $\Phi$ is an exact potential, set $P = \Phi$ and $d_i = c_i - \Phi$, which is independent of $s_i$ by exactness. Conversely $P$ is an exact potential of $P + d$.

## Depends on

- [Exact potential](../is-exact-potential.md)

## Sources

- Dov Monderer and Lloyd S. Shapley, "Potential Games", Games and Economic Behavior, 1996.
