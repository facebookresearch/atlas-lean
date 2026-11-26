# Constant-factor maximin share guarantees beyond additive valuations

For agents with monotone valuations $v_i : 2^M \to \mathbb{R}_{\ge 0}$, define $\mu_i = \max \min_k v_i(P_k)$ over partitions of $M$ into $n$ bundles. For submodular valuations a complete $\tfrac13$-MMS allocation always exists, and for XOS (fractionally subadditive) valuations a complete $\tfrac15$-MMS allocation always exists; for subadditive valuations an $\Omega(1/\log m)$-MMS allocation exists. Polynomial-time algorithms achieve constant-factor guarantees for submodular and XOS valuations given suitable oracle access.

## Proof sketch

Reduce to instances in which no single good is worth a large fraction of any agent's maximin share by allocating such goods individually (valid reductions remain valid for monotone valuations). For the remaining small goods, bag-filling with each agent's valuation, together with a property of submodular and XOS functions that a random subset of a partition bundle retains a constant fraction of its value, ensures every agent accepts some bag before goods run out. For subadditive valuations, a hierarchical bucketing of goods by value scale loses a logarithmic factor.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [XOS set functions, demand queries and value queries](../../../mechanism-design/combinatorial-and-multi-agent-contracts/xos-functions-demand-and-value-queries.md)

## Proof depends on

- [Valid reduction rules preserving maximin shares of the remaining agents](valid-reductions-maximin-share.md)

## Sources

- M. Ghodsi, M. HajiAghayi, M. Seddighin, S. Seddighin, H. Yami, "Fair Allocation of Indivisible Goods: Improvements and Generalizations", EC 2018, arXiv:1704.00222.
