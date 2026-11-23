# Line bundles on abelian varieties

This node is still to be broken down. It covers the theory of invertible sheaves on an
[abelian variety](abelian-scheme.md) $A$ over a field $k$ that the proofs of
[projectivity](abelian-varieties-are-projective.md), of the existence of the
[dual abelian variety](dual-abelian-variety.md), and of the facts on
[polarizations](polarization.md) and [Zarhin's trick](zarhin-trick.md) use. Its central results are
the theorem of the cube and the theorem of the square: for an invertible sheaf $L$ on $A$ and points
$a, b \in A(k)$,

$$t_{a+b}^* L \otimes L \cong t_a^* L \otimes t_b^* L,$$

where $t_a$ is translation by $a$, so that $\varphi_L \colon A(k) \to \operatorname{Pic}(A)$,
$a \mapsto t_a^* L \otimes L^{-1}$, is a homomorphism whose image lies in $\operatorname{Pic}^0(A)$.

A good expansion follows Milne's notes and has pages for:

- the theorem of the cube for complete geometrically irreducible varieties with base points
  (Milne, Theorem I.5.1, proved at the end of §I.5), its Corollaries I.5.2–I.5.4, in
  particular $n_A^* L \cong L^{(n^2+n)/2} \otimes (-1)_A^* L^{(n^2-n)/2}$, and the theorem of the
  square (Theorem I.5.5 and Remark I.5.6);
- the seesaw principle (Theorem I.5.16, Corollaries I.5.17 and I.5.18) and the closedness of the
  set of points over which a family of invertible sheaves on a complete variety is trivial
  (Proposition I.5.19);
- the group $K(L)$, the subgroup $\operatorname{Pic}^0(A)$ (Proposition I.8.4, Lemma I.8.8) and the
  ampleness criterion of Proposition I.8.1;
- quotients of varieties by finite groups and descent of coherent sheaves along them
  (Propositions I.8.10 and I.8.13, after Mumford's *Abelian Varieties*, pp. 66 and 70), and the
  surjectivity of $\varphi_L$ onto $\operatorname{Pic}^0(A)$ for ample $L$ (Proposition I.8.14,
  Mumford, §8, p. 77), which give the construction of the dual abelian variety in characteristic
  zero (Milne, §I.8); in positive characteristic the construction divides by a finite subgroup scheme
  (Mumford, Chapter III, as cited by Milne);
- the Riemann–Roch theorem for abelian varieties (Theorem I.11.1, after Mumford, p. 150): the degree
  of $\varphi_L$ is $\chi(L)^2$, $\chi(L) = (D^g)/g!$ for $L = \mathcal{L}(D)$ and $g = \dim A$, and
  exactly one cohomology group of $L$ is nonzero when $K(L)$ is finite; with the vanishing of the
  higher cohomology of ample invertible sheaves on $A$, it shows that an ample $L$ whose
  $\varphi_L$ is a principal polarization has a one-dimensional space of global sections, and a page
  for this consequence should cite a source for that vanishing;
- Weil pairings and the criteria for descending polarizations along isogenies (Lemma I.13.1,
  Proposition I.13.2, Proposition I.13.8 and Corollaries I.13.10 and I.13.11), on which Milne's proof
  of Zarhin's trick rests.

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties over a field

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, §5 (Theorem 5.1, Corollaries 5.2–5.4,
  Theorem 5.5, Remark 5.6, Theorem 5.16, Corollaries 5.17–5.18, Proposition 5.19), §8 (Propositions
  8.1, 8.4, 8.10, 8.13, 8.14, Lemma 8.8 and the construction of the dual), §11 (Theorem 11.1), §13
  (Lemma 13.1, Propositions 13.2 and 13.8, Corollaries 13.10 and 13.11).
- D. Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research Studies in Mathematics 5,
  Oxford University Press, 1970: the pages cited by Milne above.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses the consequence of the Riemann–Roch theorem for a
  principal polarization over an algebraically closed field, as
  `GlobalTheory.Published.principalPolarisationOneSection`.
