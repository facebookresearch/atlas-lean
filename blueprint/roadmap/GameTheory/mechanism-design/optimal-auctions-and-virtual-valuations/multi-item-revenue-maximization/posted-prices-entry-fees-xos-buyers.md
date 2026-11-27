# Sequential posted prices with entry fees approximate revenue for XOS buyers

For $m$ buyers with independent item types and XOS (fractionally subadditive) valuations over $n$ items, the better of a sequential posted price mechanism and an anonymous sequential posted price mechanism with an entry fee per buyer (both deterministic and dominant-strategy incentive compatible) achieves a constant fraction of the optimal revenue of randomized Bayesian incentive-compatible mechanisms; for valuations subadditive over independent items the same pair achieves an $O(\log n)$-approximation.

## Proof sketch

Extend the Cai–Devanur–Weinberg duality framework to subadditive buyers to obtain a revenue benchmark that decomposes into a single-dimensional part, bounded by sequential posted prices, and a core part. The core is handled by concentration of the buyer's value under independent item types (Talagrand's and Schechtman's inequalities, using that XOS functions are Lipschitz in the appropriate sense), which an entry fee extracts.

## Depends on

- [XOS set functions, demand queries and value queries](../../contracts-and-rational-cryptography/combinatorial-and-multi-agent-contracts/xos-functions-demand-and-value-queries.md)
- [Bayesian incentive compatibility](../../revelation-principle/is-bayes-incentive-compatible.md)

## Proof depends on

- [Simple mechanisms approximate optimal revenue for many additive and unit-demand buyers](simple-mechanisms-many-buyers-duality.md)
- [Simple mechanisms are constant-factor optimal for a subadditive buyer over independent items](simple-mechanisms-subadditive-buyer.md)
- [Lagrangian duality upper bounds revenue by virtual welfare under flows](duality-virtual-welfare-revenue-bound.md)

## Sources

- Y. Cai, M. Zhao, "Simple Mechanisms for Subadditive Buyers via Duality", STOC 2017, arXiv:1611.06910.
