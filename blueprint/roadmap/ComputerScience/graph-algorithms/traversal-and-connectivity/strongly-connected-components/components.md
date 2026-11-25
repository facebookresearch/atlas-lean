# Strongly connected components algorithm

Let $G$ be a directed graph and let
$v_1, \dots, v_n$ be its vertices in decreasing order of finishing time in a depth-first search of
the whole graph that takes its roots in the vertex order of $G$. For each $i$, let $C_i$ be the
list of those $v_j$, in increasing order of $j$, such that $v_i$ and $v_j$ are strongly connected
(tested by two depth-first searches). The output is the list $C_1, \dots, C_n$ with repeated
blocks removed, keeping the last occurrence of each.

The result is deterministic: within a block, vertices appear in decreasing finish order.
