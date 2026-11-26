# Sequential posted prices with entry fees approximate revenue for XOS buyers

For $m$ buyers with independent item types and XOS (fractionally subadditive) valuations over $n$ items, a sequential posted price mechanism with an entry fee per buyer achieves a constant fraction of the optimal Bayesian incentive-compatible revenue; for subadditive valuations the same type of mechanism achieves an $O(\log n)$-approximation.

## Proof sketch

Extend the Lagrangian duality framework to subadditive buyers by relaxing to an XOS-like benchmark: construct a flow whose virtual values decompose into a single-dimensional part, bounded by posted prices via a prophet-inequality argument, and a core part. The core is handled by concentration of the buyer's XOS value under independent item types, which an entry fee extracts.

## Depends on

- [Lagrangian duality upper bounds revenue by virtual welfare under flows](duality-virtual-welfare-revenue-bound.md)
- [XOS set functions, demand queries and value queries](../combinatorial-and-multi-agent-contracts/xos-functions-demand-and-value-queries.md)

## Proof depends on

- [Simple mechanisms approximate optimal revenue for many additive and unit-demand buyers](simple-mechanisms-many-buyers-duality.md)
- [Simple mechanisms are constant-factor optimal for a subadditive buyer over independent items](simple-mechanisms-subadditive-buyer.md)

## Sources

- Y. Cai, M. Zhao, "Simple Mechanisms for Subadditive Buyers via Duality", STOC 2017, arXiv:1611.06910.
