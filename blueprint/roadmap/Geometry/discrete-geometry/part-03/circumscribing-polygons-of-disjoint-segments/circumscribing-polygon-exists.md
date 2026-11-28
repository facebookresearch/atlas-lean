# Mirzaian's circumscribing polygon conjecture

Mirzaian's conjecture, for segments that are not all collinear. Let $m \in \mathbb{N}$ and let $e_0, \dots, e_{2m-1} \in \mathbb{R}^2$ be endpoints of $m$ closed segments $s_k = [e_{2k}, e_{2k+1}]$, $k = 0, \dots, m - 1$, which are nondegenerate ($e_{2k} \ne e_{2k+1}$) and pairwise disjoint. In the segment visibility graph, two distinct endpoints $e_i, e_j$ are adjacent when they are the two endpoints of the same segment, or when the open segment $(e_i, e_j)$ meets no segment $s_k$. Assume moreover that the $2m$ endpoints are not all collinear. Then there is a cyclic ordering $e_{\pi(0)}, \dots, e_{\pi(2m-1)}$ of all the endpoints ($\pi$ a permutation, indices mod $2m$) such that

- consecutive endpoints $e_{\pi(t)}$ and $e_{\pi(t+1)}$ are adjacent in the segment visibility graph, so the ordering is a Hamiltonian cycle;
- the polygon $e_{\pi(0)} \cdots e_{\pi(2m-1)}$ is simple: it has at least $3$ vertices, nondegenerate edges, and its edges meet only at the common vertex of consecutive edges;
- the polygon is circumscribing: with $K$ a compact region with nonempty interior whose frontier is the polygon, every segment is either an edge of the polygon or has its relative interior inside the interior of $K$. It is false; the refutation is [Mirzaian's circumscribing polygon conjecture is false](circumscribing-polygon-exists-refuted.md).

## Sources

- S. K. Ghosh and P. P. Goswami, "Unsolved problems in visibility graphs of points, segments and polygons", arXiv:1012.5187v4, Conjecture 9 (A. Mirzaian), https://arxiv.org/abs/1012.5187v4.
