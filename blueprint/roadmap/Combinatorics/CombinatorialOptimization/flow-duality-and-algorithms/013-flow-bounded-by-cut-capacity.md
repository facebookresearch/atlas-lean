---
article_id: af_65ba46c89a054515891a2c1c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: NetworkFlow.flow_le_cut
---

# Lemma 2 (flow bounded by cut capacity)

Let $f$ be an $s$-$t$ flow in a directed network $G$ with capacities $c$, and let $(S, \bar{S})$ be any $s$-$t$ cut with $s \in S$ and $t \in \bar{S}$. Then the value $f$ of the flow satisfies $f \leq c(S, \bar{S})$, where $c(S, \bar{S})$ is the sum of the capacities of edges from $S$ to $\bar{S}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.433 Combinatorial Optimization (Fall 2003), Flow Duality and algorithms, Sept 25-30 (Max Flow-Min Cut)](../../../../sources/v1/CombinatorialOptimization.md)
