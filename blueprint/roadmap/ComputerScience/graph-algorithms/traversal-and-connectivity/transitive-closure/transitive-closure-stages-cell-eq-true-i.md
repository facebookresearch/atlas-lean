# Invariant of the transitive-closure stages

Let $A$ be a Boolean adjacency matrix of a
directed graph on the vertices $0, \dots, n-1$ and let $k \le n$. For all vertices $i$ and $j$, the
entry $(i, j)$ of the matrix produced by the staged transitive-closure computation after its first
$k$ pivot stages is true if and only if there are vertices $i = v_0, v_1, \dots, v_m = j$ with
$m \ge 0$ such that each $A_{v_t v_{t+1}}$ is true and every intermediate vertex
$v_1, \dots, v_{m-1}$ is less than $k$.
