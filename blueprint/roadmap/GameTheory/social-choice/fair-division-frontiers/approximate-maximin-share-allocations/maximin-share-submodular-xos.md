# Constant-factor maximin share guarantees beyond additive valuations

For agents with monotone valuations $v_i : 2^M \to \mathbb{R}_{\ge 0}$ with $v_i(\emptyset) = 0$, define $\mu_i = \max \min_k v_i(P_k)$ over partitions of $M$ into $n$ bundles. For submodular valuations a complete $\tfrac13$-MMS allocation always exists, and for XOS (fractionally subadditive) valuations a complete $\tfrac15$-MMS allocation always exists; for subadditive valuations and $m = |M| \ge 2$ goods a $\tfrac{1}{10 \lceil \log m \rceil}$-MMS allocation exists. For $m \le 1$ this denominator is $0$, and an exact MMS allocation exists for all monotone valuations: with no goods every $\mu_i = 0$; with one good, giving it to the single agent when $n = 1$ is exact, and when $n \ge 2$ some bundle of every partition is empty, so every $\mu_i = 0$ and every allocation is MMS. A $\tfrac13$-MMS allocation for submodular valuations can be found in polynomial time with value queries, and a $\tfrac18$-MMS allocation for XOS valuations with demand and XOS oracles.

## Proof sketch

Normalize $\mu_i = 1$ and first allocate any single good worth at least the target factor to some agent (valid reductions remain valid for monotone valuations), so the instance is irreducible. For submodular valuations, take an allocation maximizing the bounded welfare $\sum_i \min\{2/3, v_i(A_i)\}$; if some agent had less than $1/3$, a uniformly random good outside her bundle adds, in expectation, more to her value than it removes from the bounded welfare, contradicting maximality. The XOS case runs the same exchange argument with a different threshold. Subadditive valuations are approximated by XOS valuations within a factor $O(\log m)$, which gives the logarithmic bound.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)
- [XOS set functions, demand queries and value queries](../../../mechanism-design/contracts-and-rational-cryptography/combinatorial-and-multi-agent-contracts/xos-functions-demand-and-value-queries.md)

## Proof depends on

- [Valid reduction rules preserving maximin shares of the remaining agents](valid-reductions-maximin-share.md)

## Sources

- M. Ghodsi, M. HajiAghayi, M. Seddighin, S. Seddighin, H. Yami, "Fair Allocation of Indivisible Goods: Improvements and Generalizations", EC 2018, arXiv:1704.00222.
