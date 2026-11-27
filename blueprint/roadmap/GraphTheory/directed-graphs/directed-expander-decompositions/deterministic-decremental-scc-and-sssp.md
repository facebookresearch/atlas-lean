# Deterministic decremental reachability and SCC in o(mn) total time and dense-graph approximate SSSP against adaptive adversaries

Let $G$ be a directed graph with $n$ vertices and $m$ edges undergoing adversarial edge deletions, where the adversary may adapt to the answers.

1. There are deterministic data structures for decremental single-source reachability and decremental strongly connected components with total update time $mn^{2/3+o(1)}$; reachability and same-component queries take $O(1)$ time, and a path query is answered in $|P|\cdot n^{o(1)}$ time, where $|P|$ is the length of the returned simple path.
2. If $G$ has positive edge weights with ratio of largest to smallest weight $W$, there is a deterministic data structure for decremental $(1+\epsilon)$-approximate single-source shortest paths, allowing edge deletions and weight increases, with total update time $n^{2+2/3+o(1)}\log(W)/\epsilon$, $O(1)$-time distance queries and $|P|\cdot n^{o(1)}$-time path queries.

Before this, the best adaptive bound for these problems was the $O(mn)$ total update time of Even-Shiloach trees. The bound of item 1 is $o(mn)$ for every graph. The bound of item 2 is below $mn$ only when $m \ge n^{5/3+o(1)}\log(W)/\epsilon$; for sparser graphs it does not improve on $O(mn)$, so the sub-$mn$ guarantee holds in general only for reachability and strongly connected components.

## Proof sketch

Maintain an approximate directed vertex-expander decomposition with $\phi=n^{-1/3}$, so the removed vertex set has size $\tilde O(\phi n)$ and the rest is a DAG of vertex expanders. Each expander is certified by a low-congestion embedded witness expander, which is maintained under deletions by congestion balancing, a flow method that raises capacities of over-used edges and re-routes; when the witness cannot be repaired, a sparse vertex cut is found and the cluster splits. Reachability inside expanders uses short paths through the witness, the DAG part is handled by topological order, and the $\tilde O(\phi n)$ separator vertices are handled by Even-Shiloach trees, giving $\hat O(m n^{2/3})$ total time; the SSSP structure applies the same framework to approximate topological orders.

## Depends on

- [Dynamic graph problems](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)
- [Amortized cost of an operation](../../../ComputerScience/data-structures/amortized-analysis/amortized-cost.md)
- [Strongly connected vertices](../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/strongly-connected.md)

## Proof depends on

- [Every directed graph has a phi-expander decomposition whose backward edges number O(phi m log m)](directed-expander-decomposition-existence.md)
- [Embedding an expander with low vertex congestion certifies directed vertex expansion](vertex-expansion-by-low-congestion-embedding.md)

## Sources

- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental Reachability, SCC, and Shortest Paths via Directed Expanders and Congestion Balancing", FOCS (2020), arXiv:2009.02584.
