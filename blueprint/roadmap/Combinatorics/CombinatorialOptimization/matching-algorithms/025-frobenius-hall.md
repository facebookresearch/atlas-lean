---
article_id: af_0d25d731ccd895f19e1e93f3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: SimpleGraph.hall_marriage_theorem
---

# Theorem 5 (Frobenius-Hall)

Let $G$ be a bipartite graph with vertex partition $(A, B)$. Then $A$ admits a matching into $B$ (i.e.\ a matching of size $|A|$) if and only if for every subset $X$ of $A$, $|X| \leq |\Gamma(X)|$, where $\Gamma(X)$ is the set of neighbors of $X$ in $B$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 4 (Konig)](024-konig.md)

## Sources

- [MIT 18.433 Combinatorial Optimization (Fall 2003), Matching Algorithms, Sept 4-9-11 (Bipartite graphs)](../../../../sources/v1/CombinatorialOptimization.md)
