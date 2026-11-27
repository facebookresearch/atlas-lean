# Explicit Ramanujan complexes and their local spectral expansion

For every $d \ge 3$ and prime power $q$ there is an explicit infinite family of $(d-1)$-dimensional Ramanujan complexes of type $\tilde A_{d-1}$ with all vertex degrees bounded by a function of $q$ and $d$. Every link of a $(d-3)$-face is either the point-line incidence graph of the projective plane over $\mathbb{F}_q$ (second eigenvalue $\sqrt{q}/(q+1)$), when the two missing vertex types are adjacent in the cyclic $\tilde A_{d-1}$ diagram, or the complete bipartite graph $K_{q+1,q+1}$ (second eigenvalue $0$), when they are not; hence these complexes are one-sided $\lambda$-local spectral expanders with $\lambda = O_d(1/\sqrt{q})$, which tends to $0$ as $q \to \infty$.

## Proof sketch

Existence and explicitness come from arithmetic lattices in division algebras over function fields, for which the Ramanujan property is the function-field Ramanujan conjecture proved by Lafforgue. Local spectral expansion is independent of the Ramanujan property: every vertex link is a finite spherical building whose $1$-dimensional links are projective plane incidence graphs, whose spectrum is computed exactly; trickling down handles the remaining links.

## Depends on

- [Ramanujan complexes of type Ã_{d-1}](ramanujan-complex.md)
- [Local spectral expanders (one-sided and two-sided)](local-spectral-expander.md)
- [Link of a face in a weighted complex](link-of-face.md)

## Proof depends on

- [Oppenheim's trickling-down theorem for spectral gaps](oppenheim-trickle-down.md)

## Sources

- A. Lubotzky, B. Samuels, U. Vishne, "Ramanujan complexes of type Ã_d", Israel Journal of Mathematics 149 (2005) 267-299.
- A. Lubotzky, "High dimensional expanders", Proceedings of the ICM (2018), arXiv:1712.02526.
- I. Oppenheim, "Local spectral expansion approach to high dimensional expanders Part I: Descent of spectral gaps", Discrete & Computational Geometry 59 (2018) 293-330, arXiv:1709.04431.
