# Simple polygon

A simple polygon in the Euclidean plane $\mathbb{R}^2$ consists of

- a vertex list $(v_1, \dots, v_n)$;
- a region $R \subseteq \mathbb{R}^2$ (the filled polygon);

subject to the conditions

- the frontier of $R$ equals the boundary chain of the vertex list, the union of the closed segments $[v_1, v_2], \dots, [v_{n-1}, v_n], [v_n, v_1]$;
- $R$ is closed;
- $R$ is bounded;
- $R$ has nonempty interior;
- the vertex list is simple: at least three pairwise distinct vertices, no degenerate edge, cyclically adjacent edges meeting exactly in a common endpoint, and non-adjacent edges with disjoint closed segments.
