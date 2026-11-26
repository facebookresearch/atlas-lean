# Two-thirds maximin share allocations always exist

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For every instance a complete $\tfrac23$-MMS allocation exists.

## Proof sketch

Normalize to $\mu_i = 1$ and apply valid reductions while some agent values a single good at least $2/3$. Afterwards all goods are small, and a matching-based procedure between agents and bundles of each agent's maximin partition, combined with Hall's theorem, assigns every agent a bundle worth at least $2/3$.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)

## Proof depends on

- [Valid reduction rules preserving maximin shares of the remaining agents](valid-reductions-maximin-share.md)

## Sources

- D. Kurokawa, A. D. Procaccia, J. Wang, "Fair Enough: Guaranteeing Approximate Maximin Shares", Journal of the ACM 65(2) (2018); EC 2016.
