# Simple mechanisms approximate optimal revenue for many additive and unit-demand buyers

For $m$ buyers with independent item values who are all additive over $n$ items, the optimal Bayesian incentive-compatible revenue is at most $8$ times the better of (i) selling the items separately, running Myerson's optimal auction for each item, and (ii) the VCG mechanism with a per-buyer entry fee; precisely, it is at most $6$ times the revenue of (i) plus $2$ times that of (ii). For unit-demand buyers, a sequential posted-price mechanism alone gives a $24$-approximation. The single-buyer additive case gives $\mathrm{REV} \le 2\,\mathrm{BREV} + 4\,\mathrm{SREV}$, hence $\mathrm{REV} \le 6 \max\{\mathrm{SREV}, \mathrm{BREV}\}$.

## Proof sketch

Choose a canonical flow that, for each buyer, routes from types with high value for item $j$ towards types with lower value for the same item only within the region where item $j$ is the buyer's favourite. The resulting virtual values split into a single-dimensional part, bounded by separate Myerson auctions, and a core part where virtual values equal values but are capped; the core welfare is approximated by VCG with entry fees (grand bundling for a single buyer) using concentration, extending the single-buyer core-tail analysis.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)
- [Optimal auctions for regular distributions](../remaining-clauses-of-optimal-auctions-for-regular-distributi.md)
- [Bayesian incentive compatibility](../../revelation-principle/is-bayes-incentive-compatible.md)

## Proof depends on

- [Lagrangian duality upper bounds revenue by virtual welfare under flows](duality-virtual-welfare-revenue-bound.md)
- [Core-tail decomposition of the optimal revenue](core-tail-decomposition-revenue.md)

## Sources

- Y. Cai, N. R. Devanur, S. M. Weinberg, "A Duality-Based Unified Approach to Bayesian Mechanism Design", STOC 2016; SIAM Journal on Computing 50(3) (2021), arXiv:1812.01577, Theorems 38 to 40.
- A. C.-C. Yao, "An n-to-1 Bidder Reduction for Multi-item Auctions and its Applications", SODA 2015.
