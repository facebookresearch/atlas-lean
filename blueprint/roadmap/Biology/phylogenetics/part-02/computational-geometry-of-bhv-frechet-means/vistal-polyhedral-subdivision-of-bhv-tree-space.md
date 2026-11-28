# Vistal polyhedral subdivision of BHV tree space

Let $\mathcal{T}_n$ be the BHV space of metric phylogenetic trees with $n$ leaves: one nonnegative orthant $\mathbb{R}_{\ge 0}^{n-2}$ for each binary topology (coordinates are interior edge lengths), glued along faces corresponding to shared compatible splits, with the induced geodesic metric $d$. It is a CAT(0) space, so any two trees $X, T$ are joined by a unique geodesic.

**Geodesic structure.** For trees $X$ and $T$ with no common splits, the geodesic is described by a support $(\mathcal{A},\mathcal{B}) = ((A_1,\dots,A_k),(B_1,\dots,B_k))$, a partition of the splits of $X$ into $A_1,\dots,A_k$ and of $T$ into $B_1,\dots,B_k$ such that each $A_i \cup B_{j}$ for $i > j$ is compatible (condition (P1)), satisfying the ratio-ordering and minimality conditions (P2)–(P3):

$$

\frac{\|A_1\|}{\|B_1\|} \le \frac{\|A_2\|}{\|B_2\|} \le \cdots \le \frac{\|A_k\|}{\|B_k\|},

$$

with $\|A\|$ the Euclidean norm of the edge lengths of $A$. The geodesic $\gamma(\lambda)$, $0 \le \lambda \le 1$, then has legs

$$

\Gamma^i = \Big\{ \gamma(\lambda) : \frac{\|A_i\|}{\|B_i\|} \le \frac{\lambda}{1-\lambda} < \frac{\|A_{i+1}\|}{\|B_{i+1}\|} \Big\}, \qquad i = 0,\dots,k,

$$

and length $d(X,T) = \big\| (\|A_1\|+\|B_1\|,\dots,\|A_k\|+\|B_k\|) \big\|$.

**Vistal cells.** Fix a source tree $T$. Working in squared coordinates $\xi_e = x_e^2$ on each orthant $\mathcal{O}$ (the squared tree space $\mathcal{T}_n^2$), a **previstal cell** $\mathcal{V}(T,\mathcal{O};\mathcal{A},\mathcal{B})$ is the set of $X \in \mathcal{O}$ for which a given pair $(\mathcal{A},\mathcal{B})$ is a valid support of the geodesic from $T$ to $X$. Each previstal cell is a polyhedral cone in squared coordinates, because the conditions (P2)–(P3) become linear inequalities in the $\xi_e$. A **vistal cell** is its image in $\mathcal{T}_n^2$.

**Theorem.** For a fixed source tree $T$, the vistal cells refine the natural orthant structure of $\mathcal{T}_n^2$ and form a polyhedral subdivision of $\mathcal{T}_n^2$ (the vistal subdivision). For a finite set $\mathbf{T} = \{T^1,\dots,T^r\}$, intersecting previstal cells for all $T^\ell$ inside a common orthant gives multivistal cells, which again form a polyhedral subdivision refining the orthant structure.

So the combinatorics of all geodesics from a fixed tree, and simultaneously from finitely many fixed trees, is piecewise constant on a polyhedral complex.

## Expansion

In squared coordinates $\|A_i\|^2$ is a linear function, so the ratio inequalities $\|A_i\|^2\|B_{i+1}\|^2 \le \|A_{i+1}\|^2\|B_i\|^2$ are linear in the varying tree's squared edge lengths when the source tree is fixed. One shows that faces of previstal cells are again previstal cells for degenerate supports (Proposition 3.5 and Theorem 3.25), and that two cells meet in a common face, which gives a polyhedral complex. Intersecting the subdivisions for each source tree gives the multivistal subdivision.

## Sources

- Ezra Miller, Megan Owen, J. Scott Provan, "Polyhedral computational geometry for averaging metric phylogenetic trees", arXiv (2012); Advances in Applied Mathematics (2015). Theorem 1.2, Section 3 (Propositions 3.5–3.6, Theorems 3.25 and 3.30, Corollary 3.34). <https://doi.org/10.48550/arXiv.1211.7046>. Published version: Advances in Applied Mathematics 68 (2015), 51–91, <https://doi.org/10.1016/j.aam.2015.04.002>; locators above refer to the arXiv version.
