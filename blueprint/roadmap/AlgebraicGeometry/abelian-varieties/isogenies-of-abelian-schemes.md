# Isogenies of abelian schemes

Let $S$ be a scheme and $A$, $B$ [abelian schemes](abelian-scheme.md) over $S$.

1. Every homomorphism $f \colon A \to B$ is proper and of finite presentation, and it is flat if it
   is surjective. If $f$ is fibrewise an isogeny, that is, if its restriction to every fibre is
   finite and surjective, then its kernel $G = f^{-1}(0_B)$ is a finite flat group scheme over $S$
   and the degree of $f$, the rank of $f_* \mathcal{O}_A$, is locally constant on $S$.
2. Let $g$ be the relative dimension of $A$, a locally constant function on $S$, and $n \ge 1$.
   Multiplication by $n$, $n_A \colon A \to A$, is flat, surjective and finite, and its kernel
   $A[n]$ is a finite locally free group scheme over $S$ of rank $n^{2g}$. Moreover $n_A$, and hence
   $A[n]$, is étale if and only if $g(s) = 0$ at every point $s$ of $S$ whose residue characteristic
   divides $n$; when $g$ is a positive constant, this says that $n$ is not divisible by the
   characteristic of any residue field of $S$. (On the zero-dimensional abelian scheme $A = S$ over
   $\operatorname{Spec} \mathbb{F}_p$, $p_A$ is the identity, which is étale.)
3. In particular, if $S$ is the spectrum of a separably closed field $k$ and $n$ is not divisible by
   the characteristic of $k$, then $A[n]$ is a finite étale group scheme, and $A(k)$ has exactly
   $n^{2g}$ points of order dividing $n$.

For 1, a surjective homomorphism of group schemes from a flat to a smooth group scheme is flat on
the fibres, hence flat; the kernel is the inverse image of the zero section, closed because $B$ is
separated, so proper over $S$, and it has finite fibres when $f$ is fibrewise an isogeny, hence it
is finite; being finite and flat, it has locally constant rank. For 2, $n_A$ is flat because $A$ is
flat over $S$ and $n_A$ is flat on every fibre, by the fibrewise criterion of flatness; it is proper
with finite fibres, hence finite; and on a fibre over a field it is an isogeny of degree $n^{2g}$
(Milne's Theorem I.7.2, proved with a symmetric very ample divisor $D$, for which $n_A^* D \sim n^2
D$: the projection formula $((n_A^* D)^g) = \deg(n_A) (D^g)$, with $((n^2 D)^g) = n^{2g} (D^g)$ and
$(D^g) > 0$, gives $\deg(n_A) = n^{2g}$; the degree of the pulled-back divisor is not that of $D$,
for an elliptic curve and $n = 2$, $\deg 3[0] = 3$ but $\deg 2^* (3[0]) = 12$). Being flat and of
finite presentation, $n_A$ is étale at the points of a fibre $A_s$ exactly when its restriction to
$A_s$ is, and, $A$ being commutative, so that $n_A$ is a homomorphism, it is étale on $A_s$ exactly
when its differential, multiplication by $n$ on the tangent space $\operatorname{Lie}(A_s)$ of
dimension $g(s)$, is an isomorphism: when $n$ is invertible in $k(s)$ or $g(s) = 0$. For 3, a finite
étale group scheme over a separably closed field is the constant group scheme of its $k$-points, so
the rank $n^{2g}$ of $A[n]$ is the number of points of order dividing $n$; the finite flat statement
alone counts the rank, not geometric points.

## Depends on

- [Abelian scheme](abelian-scheme.md)

## Proof depends on

- [Abelian varieties are projective](abelian-varieties-are-projective.md), for a symmetric very ample
  line bundle on a fibre
- [Theorem of the cube, theorem of the square and the seesaw principle](theorem-of-the-cube.md), for
  $n_A^* L \cong L^{n^2}$ when $L$ is symmetric
- [Intersection numbers and Riemann–Roch for nef line bundles](../birational-geometry/intersection-numbers-of-nef-line-bundles.md),
  for the projection formula 5, which gives $((n_A^* D)^g) = \deg(n_A) (D^g)$
- [Finite morphisms are the proper locally quasi-finite morphisms](../schemes-and-morphisms/zariski-s-main-theorem/finite-iff-proper-and-locally-quasi-finite.md),
  for the finiteness of the kernel when $f$ is fibrewise an isogeny, and of $n_A$: both are proper
  with finite fibres
- [Flatness and étaleness criteria for homomorphisms of group schemes](flatness-and-etaleness-criteria-for-group-schemes.md),
  for the fibrewise criterion of flatness (item 1), applied to a surjective $f$ and to $n_A$; for
  the flatness on the fibres of a surjective homomorphism onto a smooth group scheme and the
  étaleness of $n_A$ on a fibre through its differential (item 3); and for the passage from the
  fibres to $S$ (item 2)
- [Homomorphisms of abelian schemes and commutativity](homomorphisms-of-abelian-schemes.md), for the
  commutativity of $A$ (item 3), which makes $n_A$ a homomorphism, to which the criteria for
  homomorphisms of group schemes apply

## Sources

- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>:
  Proposition 2.3.15 and its proof (the first two statements), pp. 16–17.
- J. S. Milne, "Abelian varieties", in *Arithmetic Geometry* (Storrs, 1984), Springer, 1986,
  103–150; revised version of 2 January 2022, <https://www.jmilne.org/math/xnotes/AVs.pdf>:
  Proposition 20.7 and its proof, p. 44.
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Proposition 7.1, Theorem 7.2 with its
  proof and Remark 7.3, pp. 32–34.
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (10.12)
  (an isogeny is a finite surjective homomorphism, with kernel finite and flat by Mumford's
  *Geometric Invariant Theory*, Lemma 6.12).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 3 for abelian varieties over an algebraically closed field, counting the $n$-torsion
  points, as `GlobalTheory.Published.AbMulNSt`.
