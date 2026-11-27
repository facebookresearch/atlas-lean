# Braess's paradox

In Braess's network with one unit of traffic, every Wardrop equilibrium costs $3/2$ before the
zero-latency shortcut $v \to w$ is added and $2$ after it is added. Adding a link that can only
help a central planner raises the latency of every user from $3/2$ to $2$.

## Informally uses

- [All Wardrop equilibria have the same cost](cost-eq.md): it suffices to compute the cost of one
  equilibrium in each network.

## Background

- [Price of anarchy 4/3 for affine latencies](cost-le-of-affine.md): Braess's network has affine
  latencies; after the shortcut its equilibrium costs $2 = \tfrac43 \cdot \tfrac32$ times the
  optimum $3/2$, so it also attains the bound $4/3$.

## Sources

- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, §1.2, Figure 1.
- D. Braess, "Über ein Paradoxon aus der Verkehrsplanung", Unternehmensforschung 12 (1968), 258–268.
