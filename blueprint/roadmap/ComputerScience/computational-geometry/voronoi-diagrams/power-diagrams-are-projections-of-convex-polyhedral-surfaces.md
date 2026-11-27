# Power diagrams are projections of convex polyhedral surfaces

For $n \ge 1$ weighted sites $(p_i, w_i)$ in $\mathbb{R}^d$, the power of $x$ with respect to $(p_i, w_i)$ is $\|x\|^2 - h_i(x)$ with the affine function $h_i(x) = 2\langle p_i, x\rangle - \|p_i\|^2 + w_i$. Hence the power diagram is the vertical projection to $\mathbb{R}^d$ of the boundary of the convex polyhedron $\{(x, z) \in \mathbb{R}^{d+1} : z \ge h_i(x) \text{ for all } i\}$, the upper envelope of the $h_i$: the power cell of $(p_i, w_i)$ is the projection of the face of the polyhedron where the graph of $h_i$ meets its boundary, which may be empty or of dimension less than $d$, as the power cell may be. Conversely, the vertical projection of the boundary of any convex polyhedron in $\mathbb{R}^{d+1}$ that is the upper envelope of finitely many, and at least one, non-vertical hyperplanes is a power diagram.

## Depends on

- [Power diagram](power-diagram.md)

## Informally uses

- [Voronoi diagram as a projected upper envelope](voronoi-diagram-as-a-projected-upper-envelope.md)

## Sources

- F. Aurenhammer, "Voronoi diagrams — a survey of a fundamental geometric data structure", *ACM Computing Surveys* 23(3), 1991, <https://doi.org/10.1145/116873.116880>: p. 355, the statement that power diagrams are equivalent to the boundary projections of convex polyhedral surfaces
