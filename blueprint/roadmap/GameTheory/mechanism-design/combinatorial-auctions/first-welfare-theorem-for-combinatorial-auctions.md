# First welfare theorem for combinatorial auctions

If $(S, p)$ is a Walrasian equilibrium, then the allocation $S$ maximizes social welfare among all allocations of the items, for arbitrary real valuations. If moreover $v_i(\emptyset) \ge 0$ for all bidders, then $S$ also attains the optimum of the LP relaxation.

## Proof sketch

For any allocation $T$, each bidder's demand condition gives $v_i(S_i) - p(S_i) \ge v_i(T_i) - p(T_i)$; summing and using that unallocated items have zero price yields welfare dominance. For fractional solutions, scale the demand inequality by $x_{i,T}$, which requires nonnegative utilities.

## Depends on

- [Combinatorial auction LP relaxation and Walrasian equilibrium](combinatorial-auction-lp-relaxation-and-walrasian-equilibrium.md)

## Sources

- Liad Blumrosen and Noam Nisan, "Combinatorial Auctions", Algorithmic Game Theory, Cambridge University Press, 2007.
