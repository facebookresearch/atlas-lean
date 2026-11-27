# Linear extensions of a polytope and their inequality count

Let $P \subseteq \mathbb{R}^d$ be a polytope of dimension at least $1$. A linear extension of $P$ is a polyhedron $Q=\{(x,y) \in \mathbb{R}^{d+k} : Bx+Cy \le g,\ Ex+Fy=h\}$ together with the coordinate projection $\pi(x,y)=x$ such that $\pi(Q)=P$; its size is the number of rows of the inequality system $Bx+Cy \le g$, and the equations $Ex+Fy=h$ are not counted. Equivalently, $\mathrm{xc}(P)$ defined below is the minimum number of facets, counted relative to its affine hull, of a polyhedron that has an affine image equal to $P$. The extension complexity $\mathrm{xc}(P)$ is the minimum size of a linear extension of $P$. For polytopes $P \subseteq K$ we also use $\mathrm{xc}(K)$ for the relaxation $K$; the number $\mathrm{xc}(P)$ is invariant under affine isomorphism and does not increase when passing to a face of $P$ or a linear image of $P$.

## Depends on

- [Faces of a convex polytope](../../../Combinatorics/polytopes-simplicial-complexes/faces-of-convex-polytopes/faces.md)

## Sources

- Mihalis Yannakakis, "Expressing Combinatorial Optimization Problems by Linear Programs", Journal of Computer and System Sciences (1991).
- Samuel Fiorini, Serge Massar, Sebastian Pokutta, Hans Raj Tiwary, Ronald de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", STOC (2012) and Journal of the ACM (2015), arXiv:1111.0837.
