# Metric Wu planes and ordered origami planes

A metric Wu plane is a two-sorted structure of points and lines with incidence and orthogonality satisfying Wu's axioms of orthogonal geometry: incidence, the parallel axiom, an axiom of infinity, Desargues' axioms, orthogonality axioms and the existence of axes of symmetry. Adding betweenness and origami axioms gives ordered and origami planes.

**Vocabularies.** Points $P, Q, \dots$ and lines $\ell, m, \dots$ are two sorts (definable from incidence). The vocabulary $\tau_{wu}$ has the incidence relation $P \in \ell$ and the orthogonality relation $\ell \perp m$; the vocabulary $\tau_{o\text{-}wu}$ adds the betweenness relation $Be(P_1, P_2, P_3)$.

**Axioms.** A $\tau_{wu}$-structure is a *metric Wu plane* if it satisfies:

- Hilbert's incidence axioms: two distinct points lie on a unique line; every line has at least two points; there are three non-collinear points;
- the parallel axiom: through a point not on $\ell$ there is exactly one line not meeting $\ell$;
- the infinity axiom schema (InfLines), which makes a certain iterated parallel construction produce infinitely many distinct points, and the two Desargues axioms for triangles with parallel sides;
- the orthogonality axioms: $\perp$ is symmetric; through each point there is exactly one line orthogonal to a given line; two lines orthogonal to the same line are parallel or equal; through each point passes a line $\ell$ with $\ell \not\perp \ell$ (a non-isotropic line); the three altitudes of a triangle are concurrent;
- the axiom of symmetric axes (AxSymAx): any two intersecting non-isotropic lines have an axis of symmetry.

An *ordered metric Wu plane* is a $\tau_{o\text{-}wu}$-structure whose $\tau_{wu}$-reduct is a metric Wu plane and which satisfies Hilbert's order axioms for $Be$. A *Euclidean ordered metric Wu plane* is an ordered metric Wu plane satisfying the modified origami axiom (H*5): given points $P_1, P_2$ and a line $\ell_1$, if $P_2$ is closer to $\ell_1$ than to $P_1$, some line (fold) through $P_2$ reflects $P_1$ onto a point of $\ell_1$. An *ordered origami plane* satisfies (H*5) and (H*6): given points $P_1 \notin \ell_1$, $P_2 \notin \ell_2$ with $\ell_1, \ell_2$ not parallel and with the points distinct or the lines distinct, some fold reflects $P_1$ onto $\ell_1$ and $P_2$ onto $\ell_2$.

**The real plane.** $\Pi_\mathbb{R}$ is the plane over $\mathbb{R}$, with the usual points, lines, incidence, orthogonality ($a_0 a_1 + b_0 b_1 = 0$ for lines $a_i x + b_i y + c_i = 0$) and betweenness; it is an ordered origami plane.

## Depends on

None.

## Proof depends on

None.

## Expansion

Metric Wu planes are exactly the coordinate planes over Pythagorean fields of characteristic $0$, fields in which every sum of two squares is a square: the theory of metric Wu planes is bi-interpretable with the theory of Pythagorean fields of characteristic $0$ (Makowsky, building on Hall and Wu), and ordered metric Wu planes are bi-interpretable with ordered Pythagorean fields. Beklemishev, Dmitrieva and Makowsky show that Euclidean ordered metric Wu planes correspond to Euclidean fields and ordered origami planes to Vieta fields, Euclidean fields in which every element is a cube (formally real Pythagorean fields where every element is a square or minus a square are Euclidean).

## Sources

- L. Beklemishev, A. Dmitrieva and J. A. Makowsky, "Axiomatizing origami planes", in *Larisa Maksimova on Implication, Interpolation, and Definability*, Outstanding Contributions to Logic 28, Springer, 2024, pp. 353–377, doi:10.1007/978-3-031-47921-2_12; read as arXiv:2012.03250v2, <https://arxiv.org/abs/2012.03250v2>: the section "Background on geometry" (the vocabularies and the definition of metric Wu planes, ordered metric Wu planes and ordered origami planes), the section "Background on axiomatic geometry" (the axiom list), and the bi-interpretation theorems in the sections on Pythagorean, Euclidean and Vieta fields.
