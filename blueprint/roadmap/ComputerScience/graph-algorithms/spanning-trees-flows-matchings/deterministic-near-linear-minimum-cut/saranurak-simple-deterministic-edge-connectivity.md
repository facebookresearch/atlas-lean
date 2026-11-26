# Saranurak's expander-decomposition algorithm for edge connectivity of simple graphs

There is a deterministic algorithm that computes the edge connectivity and a global minimum cut of a simple connected undirected graph with $m$ edges in $m^{1+o(1)}$ time, using only a deterministic expander decomposition, local trimming and shaving of clusters, contraction, and Gabow's $\tilde O(\lambda m)$ algorithm on the contracted multigraph.

## Proof sketch

Compute a $(\phi, \epsilon)$-expander decomposition with $\phi = m^{-o(1)}$-scale conductance in $m^{1+o(1)}$ deterministic time. In each cluster repeatedly trim vertices having less than a constant fraction of their degree inside the cluster, then shave vertices having at most about half of their neighbors inside; a counting argument using that sides of non-trivial low cuts have volume at least $\delta^2$ shows that no non-trivial minimum cut separates vertices of a shaved core. Contracting the cores leaves $m^{1+o(1)}/\delta$ edges, on which Gabow's algorithm runs in $m^{1+o(1)}$ time; trivial cuts are handled by the minimum degree.

## Depends on

- [Weighted expander decompositions with volumes measured in the host graph](expander-decomposition.md)
- [Contractions preserving all non-trivial minimum cuts of a simple graph](nontrivial-mincut-preserving-contraction.md)

## Proof depends on

- [Kawarabayashi-Thorup contraction to O(m/delta) edges preserving non-trivial minimum cuts](kawarabayashi-thorup-contraction.md)

## Sources

- Thatchaphol Saranurak, "A Simple Deterministic Algorithm for Edge Connectivity", SOSA (2021), arXiv:2008.08575.
