# Associahedron and permutohedron covers of the tree-space link

Let $\mathrm{BHV}_n$ be the Billera–Holmes–Vogtmann space of phylogenetic trees with leaves labelled $0, 1, \dots, n$ and nonnegative interior edge lengths; it is a cone over the subspace $\mathcal T_n$ of trees whose interior edge lengths sum to $1$. $\mathcal T_n$ is a pure simplicial complex of dimension $n-3$ with one $(k-1)$-simplex for each tree with $k$ interior edges and $(2n-3)!!$ maximal simplices (chambers), two chambers being adjacent when their trees differ by a single rotation (nearest-neighbour interchange). Let $K_n$ be the $(n-2)$-dimensional associahedron and $P_{n-1}$ the $(n-2)$-dimensional permutohedron; their boundary complexes, dualized, embed in $\mathcal T_n$ as subcomplexes.

**Proposition (associahedra).** There are $n!/2$ distinct embeddings of the dual associahedron $K_n$ in $\mathcal T_n$, permuted by the symmetric group on the labels; together they cover $\mathcal T_n$, and each chamber lies in exactly $2^{n-2}$ of them.

**Proposition (permutohedra).** There are $\binom{n+1}{2}$ distinct embeddings of the dual permutohedron $P_{n-1}$ in $\mathcal T_n$, and each chamber corresponding to a caterpillar tree lies in exactly four of them.

**Theorem (flower).** Fix the permutohedron $P_{n-1}$ of caterpillars with leaves $0$ and $n$ at the two ends; each of its $(n-1)!$ chambers lies in a distinct associahedron $K_n$ (rooting at leaf $0$). This collection of $(n-1)!$ associahedra, the **flower**, covers $\mathcal T_n$. A chamber whose tree has $k$ interior edges off the path from leaf $0$ to leaf $n$ arises from exactly $2^k$ distinct chambers of the flower, and all the associahedra of the flower share the vertex of $\mathcal T_n$ given by the tree with one interior edge separating $\{0,n\}$ from $\{1,\dots,n-1\}$.

**Theorem (homotopy type).** $\mathcal T_n$ is homotopy equivalent to a wedge of $(n-1)!$ spheres of dimension $n-3$; in the flower picture each chamber of the permutohedron becomes a sphere once the rest of the flower is contracted to a point.

## Expansion

The dual associahedron $K_n$ parameterizes planar rooted trees with $n$ labelled leaves in a fixed order, adjacent chambers differing by a rotation. Rooting at leaf $0$, the planar orders of the remaining $n$ leaves give $n!$ labelings, identified in pairs by reversal, hence $n!/2$ embeddings; a binary tree admits $2^{n-2}$ planar embeddings up to reversal (one flip per internal vertex below the root), giving the multiplicity. The permutohedron arises from caterpillars with fixed end leaves, ordered by the remaining labels; each caterpillar chamber has two leaves at each end, giving four permutohedra through it. To cover $\mathcal T_n$, draw any tree with all leaves on one side of the $0$–$n$ path and rotate the off-path edges inside the associated associahedron until a caterpillar is reached. In the flower, contracting the contractible union of associahedra to the shared vertex leaves the $(n-1)!$ top cells of the permutohedron attached along their boundaries, each becoming an $(n-3)$-sphere, which recovers the known wedge-of-spheres homotopy type.

## Sources

- Satyan L. Devadoss, Daoji Huang, Dominic Spadacene, "Polyhedral Covers of Tree Space", arXiv (2013). Section 1 (definition of $\mathcal T_n$), Propositions 1 and 2, Theorem 3, Corollaries 4 and 5, Theorem 6. <https://doi.org/10.48550/arXiv.1311.0766>. Published version: SIAM Journal on Discrete Mathematics 28(3) (2014), 1508–1514, <https://doi.org/10.1137/130947532>; locators above refer to the arXiv version.
