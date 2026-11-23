# Isogenies of abelian schemes

Let $S$ be a scheme and $A$, $B$ [abelian schemes](abelian-scheme.md) over $S$.

1. Every homomorphism $f \colon A \to B$ is proper and of finite presentation, and it is flat if it is
   surjective. If $f$ is fibrewise an isogeny, that is, if its restriction to every fibre is finite and
   surjective, then its kernel $G = f^{-1}(0_B)$ is a finite flat group scheme over $S$ and the degree
   of $f$, the rank of $f_* \mathcal{O}_A$, is locally constant on $S$.
2. If $A$ has relative dimension $g$ and $n \ge 1$, multiplication by $n$, $n_A \colon A \to A$, is
   flat, surjective and finite, and its kernel $A[n]$ is a finite flat group scheme over $S$ of order
   $n^{2g}$. Moreover $n_A$, and hence $A[n]$, is étale if and only if $n$ is not divisible by the
   characteristic of any residue field of $S$.
3. In particular, if $S$ is the spectrum of a separably closed field $k$ and $n$ is not divisible by the
   characteristic of $k$, then $A(k)$ has exactly $n^{2g}$ points of order dividing $n$.

For 1, a surjective homomorphism of group schemes from a flat to a smooth group scheme is flat on the
fibres, hence flat; the kernel is the inverse image of the zero section, closed because $B$ is
separated, so proper over $S$, and it is quasi-finite when $f$ is fibrewise an isogeny, hence finite;
being finite and flat, it has locally constant rank. For 2, $n_A$ is flat because $A$ is flat over $S$
and $n_A$ is flat on every fibre, by the fibrewise criterion of flatness; it is proper with finite
fibres, hence finite; and on a fibre over a field it is an isogeny of degree $n^{2g}$, étale exactly when
the characteristic does not divide $n$ (Milne's Theorem I.7.2, proved with a symmetric very ample line
bundle $L$, for which $n_A^* L \cong L^{n^2}$, and the equality of degrees of a very ample divisor and
its pull-back). Then 3 follows, the points of $A[n]$ over $k$ being distinct and $k$-rational.

## Depends on

- [Abelian scheme](abelian-scheme.md)

## Proof depends on

- [Abelian varieties are projective](abelian-varieties-are-projective.md), for a symmetric very ample
  line bundle on a fibre
- [Theorem of the cube, theorem of the square and the seesaw principle](theorem-of-the-cube.md), for
  $n_A^* L \cong L^{n^2}$ when $L$ is symmetric

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
  (an isogeny is a finite surjective homomorphism, with kernel finite and flat by Mumford's *Geometric
  Invariant Theory*, Lemma 6.12).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) states 3 for abelian varieties over an algebraically closed field,
  counting the $n$-torsion points, as `GlobalTheory.Published.AbMulNSt`.
