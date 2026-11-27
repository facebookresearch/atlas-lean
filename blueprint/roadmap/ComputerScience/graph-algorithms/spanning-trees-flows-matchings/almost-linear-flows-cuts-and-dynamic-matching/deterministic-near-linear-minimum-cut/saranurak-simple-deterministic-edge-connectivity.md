# Saranurak's expander-decomposition algorithm for edge connectivity of simple graphs

There is a deterministic algorithm that computes the edge connectivity and a global minimum cut of a simple connected undirected graph with $m$ edges in $m^{1+o(1)}$ time, using only a deterministic expander decomposition, local trimming and shaving of clusters, contraction, and Gabow's $\tilde O(\lambda m)$ algorithm on the contracted multigraph.

## Proof sketch

Compute deterministically, in $m^{1+o(1)}$ time, an expander decomposition with conductance $\phi = 40/\delta$ and $m^{1+o(1)}/\delta$ inter-cluster edges. In each cluster repeatedly trim vertices with fewer than $2\deg(v)/5$ neighbors inside the cluster, then shave, once, every vertex with at most $\deg(v)/2 + 1$ neighbors inside. Using the expansion of the cluster and simplicity of $G$, no non-trivial minimum cut separates two vertices of a shaved core. Contracting the cores leaves $m^{1+o(1)}/\delta$ edges, so Gabow's $O(\lambda m)$-time algorithm with $\lambda \le \delta$ runs on the contracted graph in $m^{1+o(1)}$ time; returning the minimum of its answer and $\delta$ accounts for the trivial cuts.

## Depends on

- [(phi, epsilon)-expander decompositions of an undirected graph](../../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/phi-epsilon-expander-decomposition.md)
- [Contractions preserving all non-trivial minimum cuts of a simple graph](nontrivial-mincut-preserving-contraction.md)

## Sources

- Thatchaphol Saranurak, "A Simple Deterministic Algorithm for Edge Connectivity", SOSA (2021), arXiv:2008.08575.
