---
article_id: af_9534043eb1e55e4d5a4975da
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: NetworkFlow.isMaxFlow_iff_noAugmentingPath
---

# Theorem 3 (max-flow no augmenting path)

An $s$-$t$ flow $f$ in a directed network $G$ is of maximum value if and only if there is no $f$-augmenting path in $G$; equivalently, no directed $s$-$t$ path in the residual graph $\operatorname{Res}(G)$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lemma 2 (flow bounded by cut capacity)](013-flow-bounded-by-cut-capacity.md)

## Sources

- [MIT 18.433 Combinatorial Optimization (Fall 2003), Flow Duality and algorithms, Sept 25-30 (Max Flow-Min Cut)](../../../../sources/v1/CombinatorialOptimization.md)
