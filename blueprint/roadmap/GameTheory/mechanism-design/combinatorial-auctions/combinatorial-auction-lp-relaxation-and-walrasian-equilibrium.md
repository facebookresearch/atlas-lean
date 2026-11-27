# Combinatorial auction LP relaxation and Walrasian equilibrium

In a combinatorial auction with finitely many items $M$ and bidders $N$ with valuations $v_i : 2^M \to \mathbb{R}$, the *LP relaxation* (LPR) maximizes $\sum_{i, S} x_{i,S} v_i(S)$ subject to $\sum_S x_{i,S} \le 1$ for each bidder, $\sum_i \sum_{S \ni j} x_{i,S} \le 1$ for each item, and $x \ge 0$; its dual (DLPR) has bidder utilities $u_i \ge 0$ and item prices $p_j \ge 0$ with $u_i \ge v_i(S) - \sum_{j \in S} p_j$. A *Walrasian equilibrium* is an allocation $(S_i)$ of disjoint bundles and item prices $p \ge 0$ such that each $S_i$ is a demanded bundle (maximizes $v_i(S) - p(S)$) and every unallocated item has price $0$.

## Depends on

- [Social welfare](../vickrey-clarke-groves-mechanisms/welfare.md)

## Sources

- Liad Blumrosen and Noam Nisan, "Combinatorial Auctions", Algorithmic Game Theory, Cambridge University Press, 2007.
