# Polarization

Let $A$ be an [abelian variety](abelian-scheme.md) over a field $k$, with
[dual abelian variety](dual-abelian-variety.md) $A^\vee$, and let $\bar k$ be an algebraic closure of
$k$. For an invertible sheaf $L$ on $A$, the sheaf $m^* L \otimes p^* L^{-1} \otimes q^* L^{-1}$ on
$A \times A$ (with $m$ the group law and $p$, $q$ the projections) is a family of sheaves in
$\operatorname{Pic}^0$ trivial along $\{0\} \times A$, and so defines a homomorphism
$\varphi_L \colon A \to A^\vee$, given on points by $a \mapsto t_a^* L \otimes L^{-1}$.

A **polarization** of $A$ is an isogeny $\lambda \colon A \to A^\vee$ such that over $\bar k$ it
becomes $\varphi_L$ for some ample invertible sheaf $L$ on $A_{\bar k}$. Its degree is its degree as
an isogeny, a polarized abelian variety is a pair $(A, \lambda)$, and $\lambda$ is **principal** if
it has degree $1$, that is, if it is an isomorphism. This is not quite the same as requiring
$\lambda = \varphi_L$ for an ample invertible sheaf $L$ on $A$ itself.

For an abelian scheme $A \to S$ with dual abelian scheme $A^t \to S$, a polarization is an isogeny
$\lambda \colon A \to A^t$ such that for every geometric point $s$ of $S$ there is an ample divisor $D$
on the fibre $A_s$ with $\lambda_s = \varphi_D$; it is principal if it is an isomorphism. A
polarization is symmetric: $\lambda = \lambda^t \circ \kappa$, where $\kappa \colon A \to A^{tt}$ is
the canonical isomorphism.

## Depends on

- [Dual abelian variety](dual-abelian-variety.md)
- [Abelian scheme](abelian-scheme.md), for abelian schemes and isogenies
- [Line bundles on abelian varieties](line-bundles-on-abelian-varieties.md), for the theorem of the
  square, which puts the restrictions of $m^* L \otimes p^* L^{-1}$ in $\operatorname{Pic}^0$ and
  makes $\varphi_L$ a homomorphism

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, §11, p. 53 (polarizations, their
  degree, principal polarizations, and the remark that this is not the same as $\lambda = \varphi_L$
  with $L$ on $A$, after Milne 1986, 13.2), and §8, pp. 34–40 ($\varphi_L$, Lemma 8.8 and the sheaf
  $m^* L \otimes p^* L^{-1} \otimes q^* L^{-1}$).
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (10.12)
  (the dual abelian scheme $A^t$, after Mumford's *Geometric Invariant Theory*, 6.8; polarizations of
  abelian schemes, after Mumford's *Abelian Varieties*, p. 60, and *Geometric Invariant Theory*,
  Definition 6.3; symmetry of polarizations).
