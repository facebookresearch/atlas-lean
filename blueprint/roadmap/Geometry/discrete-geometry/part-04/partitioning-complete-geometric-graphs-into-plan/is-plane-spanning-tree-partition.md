# Partitions into plane spanning trees

Let $p_1, \dots, p_m \in \mathbb{R}^2$ and let $c$ assign to each ordered pair $(i, j)$ of indices a colour $c(i, j) \in \{1, \dots, n\}$. The colouring $c$ partitions the edge set of the complete geometric graph on the points $p_i$ into $n$ plane spanning trees when:

- $c(i, j) = c(j, i)$ for all $i, j$;
- for every colour $k$, the graph on the vertex set $\{1, \dots, m\}$ with an edge $\{i, j\}$ for each $i \ne j$ with $c(i, j) = k$ is a tree (connected and acyclic);
- for every colour $k$ and all edges $\{i, j\}$, $\{i', j'\}$ of colour $k$ with $i, j, i', j'$ pairwise distinct, the segments $[p_i, p_j]$ and $[p_{i'}, p_{j'}]$ are disjoint.

The values $c(i, i)$ play no role.
