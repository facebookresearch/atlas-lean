# Simple mechanisms approximate optimal revenue for many additive and unit-demand buyers

For $m$ buyers with independent item values who are each additive (or each unit-demand) over $n$ items, there are constants $c_A, c_U$ such that the optimal revenue is at most $c_A$ times the better of (i) selling items separately via optimal Myerson auctions per item and (ii) a posted-price-with-entry-fee mechanism (an entry fee per buyer followed by item prices); for unit-demand buyers sequential posted pricing alone gives a constant-factor approximation. The constants are explicit and small, and the single-buyer additive case recovers the bound $\mathrm{REV} \le 6 \max\{\mathrm{SREV}, \mathrm{BREV}\}$.

## Proof sketch

Choose a canonical flow that, for each buyer, routes from types with high value for item $j$ towards types with lower value for the same item only within the region where item $j$ is the buyer's favourite. The resulting virtual values split into a single-dimensional part, bounded by separate Myerson auctions, and a core part where virtual values equal values but are capped; the core welfare is approximated by entry-fee mechanisms using concentration, extending the single-buyer core-tail analysis.

## Depends on

- [Lagrangian duality upper bounds revenue by virtual welfare under flows](duality-virtual-welfare-revenue-bound.md)
- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Proof depends on

- [Lagrangian duality upper bounds revenue by virtual welfare under flows](duality-virtual-welfare-revenue-bound.md)
- [Core-tail decomposition of the optimal revenue](core-tail-decomposition-revenue.md)

## Sources

- Y. Cai, N. R. Devanur, S. M. Weinberg, "A Duality-Based Unified Approach to Bayesian Mechanism Design", STOC 2016; SIAM Journal on Computing 50(3) (2021), arXiv:1812.01577.
- A. C.-C. Yao, "An n-to-1 Bidder Reduction for Multi-item Auctions and its Applications", SODA 2015.
