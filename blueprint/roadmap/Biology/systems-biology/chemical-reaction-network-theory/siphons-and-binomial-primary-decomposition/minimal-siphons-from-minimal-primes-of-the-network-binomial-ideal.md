# Minimal siphons from minimal primes of the network binomial ideal

Let $G$ be a chemical reaction network with species $c_1,\dots,c_s$ and complexes $c^{y_1},\dots,c^{y_n}$. Work in the ring $R=\mathbb Q[c_1,\dots,c_s]/\langle c_1c_2\cdots c_s\rangle$ of polynomial functions on the union of the coordinate hyperplanes, and associate to $G$ the ideals

$$
I_G=\big\langle c^{y_i}(c^{y_j}-c^{y_i}):c^{y_i}\to c^{y_j}\in G\big\rangle,\qquad J_G=\big\langle c^{y_j}-c^{y_i}:c^{y_i}\to c^{y_j}\in G\big\rangle,\qquad M_G=\langle c^{y_1},\dots,c^{y_n}\rangle.
$$

$I_G$ records the directed reactions, $J_G$ the underlying undirected graph, and $M_G$ the complexes.

**Theorem.** The minimal siphons of $G$ are the inclusion-minimal sets

$$
\{i\in[s]:c_i\in\mathfrak P\},
$$

where $\mathfrak P$ ranges over the minimal primes of $I_G$. If every connected component of $G$ is strongly connected, $I_G$ may be replaced by $J_G$. If $G$ is strongly connected, it may be replaced by the monomial ideal $M_G$.

Minimal siphons can therefore be computed by primary decomposition in computer algebra. Refined versions, which saturate by a monomial ideal built from the stoichiometric or conservation relations, return only the siphons relevant to some, or to a given, compatibility class. In particular, no siphon is relevant, and no invariant polyhedron has a boundary steady state, exactly when that saturation is the unit ideal.

## Depends on

- [Boundary steady states lie on siphon faces](boundary-steady-states-lie-on-siphon-faces.md)

## Proof sketch

The complex variety $V(I_G)$ consists of points with at least one zero coordinate that satisfy $\gamma^{y_i}(\gamma^{y_j}-\gamma^{y_i})=0$ for each reaction. The siphon condition says exactly that the 0/1 vector $\gamma$ with zero set $Z$ satisfies these equations: if the product contains a zero species, so must the reactant. Minimal primes of $I_G$ correspond to maximal irreducible pieces of $V(I_G)$, whose minimal zero sets are the minimal siphons. In the strongly connected case every complex is linked in both directions, so on the zero set a complex vanishes if and only if all complexes in its component do, which reduces the problem to monomials.

## Sources

- Anne Shiu and Bernd Sturmfels, "Siphons in Chemical Reaction Networks", *Bulletin of Mathematical Biology* 72 (2010), 1448–1463, <https://doi.org/10.1007/s11538-010-9502-y>. Preprint version: arXiv:0904.4529 (2009), Section 3 (ideals $I_G,J_G,M_G$, Theorem 3.1, Theorem 3.2, Theorem 3.5); published in Bulletin of Mathematical Biology 72 (2010), <https://doi.org/10.48550/arXiv.0904.4529>.
