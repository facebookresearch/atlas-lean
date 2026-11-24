# Line bundles on abelian varieties

This node is still to be broken down. It covers the results on line bundles on an
[abelian variety](abelian-scheme.md) $A$ of dimension $g$ over a field $k$ that come after the
construction of the [dual abelian variety](dual-abelian-variety.md) $A^\vee$, and that the facts on
[polarizations](polarization.md) and [Zarhin's trick](zarhin-trick.md) use; the earlier results, the
theorems of the cube and of the square, the seesaw principle and the group $K(L)$, are in
[Theorem of the cube, theorem of the square and the seesaw principle](theorem-of-the-cube.md). The
targets are:

1. For an ample line bundle $L$, the homomorphism $\varphi_L \colon A \to A^\vee$ is an isogeny with
   kernel $K(L)$; it is surjective as a morphism of schemes, hence on points over an algebraic
   closure of $k$, but not in general on $k$-points: for the elliptic curve $E \colon y^2 = x^3 - x$
   over $\mathbb{R}$ and $L = \mathcal{O}(2[0])$, identifying $E^\vee$ with $E$, $\varphi_L$ is
   multiplication by $\pm 2$, and the doubles of the points of $E(\mathbb{R})$, which has two
   connected components, lie in the identity component. Over an algebraically closed field every
   class in $\operatorname{Pic}^0(A)$ is of the form $t_a^* L \otimes L^{-1}$.
2. (Riemann–Roch.) For $L = \mathcal{O}(D)$, $\chi(L) = (D^g)/g!$, and $\deg \varphi_L = \chi(L)^2$.
3. (Vanishing theorem.) If $K(L)$ is finite, there is a unique integer $i(L)$, $0 \le i(L) \le g$,
   with $H^{i(L)}(A, L) \ne 0$, and $i(L^{-1}) = g - i(L)$; moreover $L$ is ample if and only if
   $K(L)$ is finite and $i(L) = 0$. Hence for ample $L$, $H^i(A, L) = 0$ for $i > 0$ and $h^0(A,
   L)^2 = \chi(L)^2 = \deg \varphi_L$; in particular, if $\varphi_L$ is an isomorphism, then $h^0(A,
   L) = 1$.
4. (Weil pairings and descent of polarizations.) For a symmetric isogeny $\lambda \colon A \to
   A^\vee$, the pairing $e_\lambda$ on the scheme-valued points of $\operatorname{Ker}(\lambda)$;
   for an isogeny $f \colon A \to B$, a symmetric isogeny $\mu \colon B \to B^\vee$ with $\lambda =
   f^\vee \circ \mu \circ f$ exists if and only if $\operatorname{Ker}(f) \subset
   \operatorname{Ker}(\lambda)$ is totally isotropic for $e_\lambda$, it is then unique, and it is a
   polarization exactly when $\lambda$ is; for $\alpha \in M_r(\mathbb{Z})$ the endomorphism
   $[\alpha]$ of $A^r$ has degree $\det(\alpha)^{2g}$, with the convention that a homomorphism that
   is not an isogeny has degree $0$ (so that the formula also covers singular $\alpha$, as in van
   der Geer–Moonen's proof of (11.28)), and $[\beta]^\vee = [{}^t \beta]$ for an integral $r \times
   s$ matrix $\beta$.
5. Every finite subgroup scheme of $A$, for instance the kernel of an isogeny, is contained in
   $A[m]$ for some integer $m \ge 1$.

That $\varphi_L$ is an isogeny for ample $L$, hence surjective as a morphism of schemes, is the
second target on the [dual abelian variety](dual-abelian-variety.md) (van der Geer–Moonen, Theorem
(6.18); over an algebraically closed field, Milne's Proposition I.8.14, after Mumford's *Abelian
Varieties*, §8). A good expansion has pages for: Mumford's Riemann–Roch and vanishing theorems
(Mumford, §16; Milne, Theorem I.11.1; Robert, Theorem 2.2.10, and Proposition 2.3.14 over a base);
theta groups and the Weil pairings $e_\lambda$, with the descent criterion of van der Geer and
Moonen (Propositions (11.21), (11.25) and (11.28), through their Example (8.26)); and, for 5, the
existence for an isogeny $f$ of an isogeny $h$ and an integer $n \ne 0$ with $h \circ f = n_A$ (used
in the proof of Conrad's Proposition 4.1), or Deligne's theorem that a finite commutative group
scheme over a field is killed by its order. Milne's Lemma I.13.1, Proposition I.13.2 and Corollaries
I.13.10–I.13.11 are the case of kernels of order prime to the characteristic.

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties over a field
- [Dual abelian variety](dual-abelian-variety.md), for $A^\vee$, $\varphi_L$ and dual homomorphisms
- [Theorem of the cube, theorem of the square and the seesaw principle](theorem-of-the-cube.md), for
  $K(L)$
- [Isogenies of abelian schemes](isogenies-of-abelian-schemes.md), for isogenies and their degrees
- [Polarization](polarization.md), for the polarizations whose descent 4 describes

## Proof depends on

- [Dual abelian variety](dual-abelian-variety.md), for $\varphi_L$, an isogeny for ample $L$ (its
  item 2), which gives the surjectivity in 1, and for the dual homomorphisms used in 1 and 4
- [Theorem of the cube, theorem of the square and the seesaw principle](theorem-of-the-cube.md), for
  the theorem of the square and the group $K(L)$
- [Isogenies of abelian schemes](isogenies-of-abelian-schemes.md), for the degrees of isogenies and
  of $n_A$, used in 2, 4 and 5
- [Standard results of coherent cohomology on projective varieties](../birational-geometry/standard-results-of-coherent-cohomology.md),
  for the Riemann–Roch polynomial and Serre duality used in 2 and 3
- [Smith normal form with a divisibility chain](../../LinearAlgebra/eigenvalues-and-canonical-forms/smith-normal-form/exists-smith-normal-form-dvd-chain.md),
  for the reduction of a nonsingular integral matrix to elementary divisors, applied to the image of
  $\alpha$ in $\mathbb{Z}^r$, in the degree formula of 4 (van der Geer–Moonen, (11.28) (i))

## Sources

- G. van der Geer and B. Moonen, *Abelian Varieties*, book draft, Chapter VI, "The Picard scheme of
  an abelian variety", <https://www.math.ru.nl/personal/bmoonen/BookAV/DualAV1.pdf>: Theorem (6.18),
  p. 95; and Chapter XI, "Polarizations and Weil pairings",
  <https://www.math.ru.nl/personal/bmoonen/BookAV/PolWp.pdf>: Propositions (11.21), (11.25) and
  (11.28), pp. 166–170.
- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>: Theorem
  2.2.10 (Riemann–Roch, $\deg \varphi_L = \chi(L)^2$, vanishing theorem, ampleness criterion;
  referring to Mumford, §16) and Proposition 2.3.14 (over a base).
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, §8 (Proposition 8.14, in the
  construction preceding Proposition 8.10, where $k$ is assumed algebraically closed), §11 (Theorem
  11.1) and §13 (Lemma 13.1, Proposition 13.2, Corollaries 13.10 and 13.11).
- D. Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research Studies in Mathematics 5,
  Oxford University Press, 1970: §8 and §16, as cited above.
- J. Tate and F. Oort, "Group schemes of prime order", Ann. Sci. École Norm. Sup. (4) 3 (1970),
  1–21: §1 (Deligne's theorem).
- B. Conrad, "Semistable reduction for abelian varieties", seminar notes, Stanford, 2011,
  <http://math.stanford.edu/~conrad/mordellsem/Notes/L13.pdf>: the proof of Proposition 4.1.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the consequence of 3 for a principal polarization over an algebraically closed field, that
  its line bundle has a one-dimensional space of global sections, as
  `GlobalTheory.Published.principalPolarisationOneSection`.
