# Herbrand quotient of the T-units of a cyclic extension

Let $L/K$ be a cyclic extension of number fields of degree $n$ with Galois group $G$, let $S$ be a finite
set of places of $K$ containing the infinite places, and let $T$ be the set of places of $L$ above $S$.
The group of $T$-units

$$U(T) = \{ \alpha \in L^\times : \mathrm{ord}_w(\alpha) = 0 \text{ for every finite place } w \notin T \}$$

is stable under $G$. Its Herbrand quotient
$h(U(T)) = |\hat H^0(G, U(T))| / |\hat H^{-1}(G, U(T))|$ is defined and

$$n \cdot h(U(T)) = \prod_{v \in S} n_v,$$

where $n_v = [L_w : K_v]$ is the local degree at $v$, for any place $w$ of $L$ above $v$.

Milne's proof compares two $G$-stable full lattices in the real representation
$V = \mathrm{Hom}(T, \mathbb{R}) = \mathbb{R}^T$ of $G$, on which $\sigma$ acts by
$(\sigma f)(w) = f(\sigma^{-1} w)$. The first is $N = \mathrm{Hom}(T, \mathbb{Z})$; the orbits of $G$ on
$T$ are the sets of places above each $v \in S$, so $N$ is the sum over $v \in S$ of the modules induced
from the trivial module $\mathbb{Z}$ of the decomposition groups $G_v$, and $h(N) = \prod_{v \in S} n_v$
by Shapiro's lemma. The second is $M = M_0 + \mathbb{Z}(1, \dots, 1)$, where $M_0$ is the image of
$\lambda \colon U(T) \to V$, $\alpha \mapsto (\log |\alpha|_w)_{w \in T}$; by
[Dirichlet's S-unit theorem](../../discriminants-ramification/s-unit-theorem.md) for $L$ and $T$, $M_0$ is
a full lattice in the hyperplane $\sum_w x_w = 0$ and the kernel of $\lambda$ is the finite group of roots
of unity of $L$. Hence $h(U(T)) = h(M_0)$ and $h(M) = n \, h(M_0)$, and the
[two lattices have the same Herbrand quotient](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-of-lattices.md).

## Depends on

- [Herbrand quotient](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient.md)
- [Places of a number field](../places-of-a-number-field/place.md)

## Proof depends on

- [Dirichlet's S-unit theorem](../../discriminants-ramification/s-unit-theorem.md), for $L$ and the set $T$, in its logarithmic form
- [Herbrand quotients of lattices in a real representation of a cyclic group](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-of-lattices.md)
- [Herbrand quotients agree across a map with finite kernel and cokernel](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-finite-kernel-cokernel.md), for $h(U(T)) = h(M_0)$, the kernel of $\lambda$ being finite
- [Multiplicativity of the Herbrand quotient in short exact sequences](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-mul-of-short-exact.md), for $h(M) = h(M_0) \, h(\mathbb{Z}) = n \, h(M_0)$
- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for Shapiro's lemma for Tate cohomology (its item 1) and the Tate cohomology of the trivial module $\mathbb{Z}$, which gives $h(\mathbb{Z}) = n$ and $h(G_v, \mathbb{Z}) = n_v$ (its item 5)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Proposition VII.3.1 (the statement, with
  $S \supseteq S_\infty$ as fixed at the start of Section VII.3) and its proof, through Lemmas VII.3.2,
  VII.3.4 and VII.3.5.
