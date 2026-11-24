# Index of the n-th powers in a local field of characteristic zero

Let $K$ be a local field of characteristic $0$, that is, $\mathbb{R}$, $\mathbb{C}$ or a finite extension of
$\mathbb{Q}_p$, with normalized absolute value $|\cdot|$ (the square of the usual one on $\mathbb{C}$), and
let $n \ge 1$. Let $\mu_n(K)$ be the group of $n$-th roots of unity in $K$. Then

$$(K^\times : K^{\times n}) = \frac{n \, |\mu_n(K)|}{|n|}.$$

If $K$ is non-archimedean, with unit group $U$, then moreover $(U : U^n) = |\mu_n(K)| / |n|$.

For example, if $K$ contains a primitive $n$-th root of unity, then
$(K^\times : K^{\times n}) = n^2 / |n|$, and this is $n^2$ when $K$ is non-archimedean of residue
characteristic prime to $n$.

Milne's proof: for $\mathbb{C}$ and $\mathbb{R}$ the formula is checked directly. For $K$ non-archimedean,
$K^\times \cong U \times \mathbb{Z}$, so $(K^\times : K^{\times n}) = n \, (U : U^n)$. Let $G$ be a cyclic group
of order $n$ acting trivially; for an abelian group $M$ its Herbrand quotient is
$h_n(M) = (M : nM) / |M[n]|$, where $M[n]$ is the $n$-torsion. The exponential map identifies an open
subgroup of finite index of $\mathcal{O}_K$ with an open subgroup of finite index of $U$
([the p-adic exponential](p-adic-exponential.md)), so
$h_n(U) = h_n(\mathcal{O}_K) = (\mathcal{O}_K : n\mathcal{O}_K) = |n|^{-1}$ because
[Herbrand quotients agree across a map with finite kernel and cokernel](../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-finite-kernel-cokernel.md);
and $U[n] = \mu_n(K)$, which gives $(U : U^n) = |\mu_n(K)| \, h_n(U)$.

## Depends on

- [Residue field of a local ring](../../RingTheory/local-rings/local-rings-and-residue-fields/residue-field-local-ring.md), for the residue characteristic in the example

## Proof depends on

- [Herbrand quotients agree across a map with finite kernel and cokernel](../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-finite-kernel-cokernel.md), for the trivial action of a cyclic group of order $n$
- [The p-adic exponential on a neighbourhood of zero](p-adic-exponential.md), for open subgroups of finite index of $\mathcal{O}_K$ and $U$ that are isomorphic
- [Natural numbers that are units in a local ring](../../RingTheory/ramification/ramification-index-and-inertia-degree/is-unit-nat-cast-iff-ring-char-not-dvd.md), for $\lvert n \rvert = 1$ in the example: $n$ is a unit of $\mathcal{O}_K$ when the residue characteristic does not divide $n$

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Proposition VII.6.8 (the statement) and its proof,
  which uses the exponential map as in the proof of Lemma III.2.4.
