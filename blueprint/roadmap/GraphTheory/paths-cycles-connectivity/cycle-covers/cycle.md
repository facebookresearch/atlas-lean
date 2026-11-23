# Cycles in a graph

A cycle in a simple graph $G$ consists of a base vertex $v$ of $G$
together with a closed walk $v = v_0, v_1, \dots, v_n = v$ in $G$ such that $n \ge 1$, the $n$
edges $v_{k-1} v_k$ of the walk are pairwise distinct, and the vertices $v_1, \dots, v_n$ are
pairwise distinct. In a simple graph this forces $n \ge 3$.

The base vertex and the direction of traversal are part of the data, so a single cycle subgraph
of $G$ arises from several such cycles.
