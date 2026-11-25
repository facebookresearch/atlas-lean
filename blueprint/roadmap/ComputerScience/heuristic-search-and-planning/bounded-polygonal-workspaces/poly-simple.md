# Simple vertex list

For a finite list of points $(v_1, \dots, v_n)$ of the Euclidean plane $\mathbb{R}^2$, its cyclic edge list is $((v_1, v_2), (v_2, v_3), \dots, (v_{n-1}, v_n), (v_n, v_1))$ (empty for the empty list, and $((v_1, v_1))$ for a one-point list). Let $e_0, \dots, e_{m-1}$ be the entries of the cyclic edge list, with $e_i = (u_i, w_i)$. The vertex list is simple when

- it has at least $3$ vertices;
- its vertices are pairwise distinct;
- no edge is degenerate: $u_i \neq w_i$ for every edge;
- for all indices $i \neq j$ below $m$: if $i$ and $j$ are cyclically adjacent ($(i+1) \bmod m = j$ or $(j+1) \bmod m = i$), then some common endpoint $p \in \{u_i, w_i\} \cap \{u_j, w_j\}$ satisfies $[u_i, w_i] \cap [u_j, w_j] = \{p\}$; otherwise the closed segments $[u_i, w_i]$ and $[u_j, w_j]$ are disjoint.
