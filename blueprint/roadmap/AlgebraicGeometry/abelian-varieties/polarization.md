# Polarization

Let $A$ be an [abelian variety](abelian-scheme.md) over a field $k$, with
[dual abelian variety](dual-abelian-variety.md) $A^\vee$, and let $\bar k$ be an algebraic closure of
$k$. For an invertible sheaf $L$ on $A$, let $\varphi_L \colon A \to A^\vee$ be the homomorphism
classified by the Mumford bundle $m^* L \otimes p^* L^{-1} \otimes q^* L^{-1}$ on $A \times A$ (with $m$
the group law and $p$, $q$ the projections), given on points by $a \mapsto t_a^* L \otimes L^{-1}$.

A **polarization** of $A$ is an isogeny $\lambda \colon A \to A^\vee$ such that over $\bar k$ it
becomes $\varphi_L$ for some ample invertible sheaf $L$ on $A_{\bar k}$. Its degree is its degree as
an isogeny, a polarized abelian variety is a pair $(A, \lambda)$, and $\lambda$ is **principal** if
it has degree $1$, that is, if it is an isomorphism. This is not quite the same as requiring
$\lambda = \varphi_L$ for an ample invertible sheaf $L$ on $A$ itself.

For an abelian scheme $A \to S$ with [dual abelian scheme](dual-abelian-scheme.md) $A^t \to S$, a
polarization is an [isogeny](isogenies-of-abelian-schemes.md) $\lambda \colon A \to A^t$ such that
for every geometric point $s$ of $S$ there is an ample divisor $D$ on the fibre $A_s$ with
$\lambda_s = \varphi_D$; it is principal if it is an isomorphism. A polarization is symmetric:
$\lambda = \lambda^t \circ \kappa$, where $\lambda^t$ is the dual homomorphism and $\kappa \colon A
\to A^{tt}$ the biduality isomorphism; over a field this is the identity $\varphi_L = \varphi_L^\vee
\circ \kappa_A$ of the dual abelian variety. Over an arbitrary base it follows from the field case.
The homomorphism $\delta = \lambda - \lambda^t \circ \kappa \colon A \to A^t$ is zero on every
geometric fibre, since $\lambda^t$ and $\kappa$ restrict there to the dual homomorphism and the
biduality isomorphism of the dual abelian varieties. Let $s \in S$, let $S_0$ be an affine open
neighbourhood of $s$ and $U \subset A^t_{S_0}$ an affine open subscheme containing the zero of
$A^t_s$. As $\pi \colon A \to S$ is proper, the points of $S_0$ over which $\delta$ maps the fibre
of $A$ into $U$ form an open neighbourhood of $s$; let $V$ be an affine open neighbourhood of $s$
inside it. Then $\delta$ maps $A_V$ into the affine $V$-scheme $U \times_{S_0} V$, and as $(\pi_V)_*
\mathcal{O}_{A_V} = \mathcal{O}_V$ it factors through $V$; as it preserves the zero section, it is
zero on $A_V$.

## Depends on

- [Dual abelian variety](dual-abelian-variety.md), for $A^\vee$ and $\varphi_L$
- [Dual abelian scheme](dual-abelian-scheme.md), for $A^t$, dual homomorphisms and biduality over a
  base
- [Isogenies of abelian schemes](isogenies-of-abelian-schemes.md), for isogenies and their degrees
- [Abelian scheme](abelian-scheme.md), for abelian schemes

## Proof depends on

- [Dual abelian variety](dual-abelian-variety.md), for $\varphi_L = \varphi_L^\vee \circ \kappa_A$
  (item 4), the symmetry of a polarization over a field
- [Dual abelian scheme](dual-abelian-scheme.md), for the dual homomorphism $\lambda^t$ and the
  biduality isomorphism $\kappa$ over $S$, which restrict on the fibres to those of the dual abelian
  varieties
- [Rigidity lemma](rigidity-lemma.md), for the cohomological flatness $(\pi_V)_* \mathcal{O}_{A_V} =
  \mathcal{O}_V$ of an abelian scheme after every base change (Robert, Lemma A.2.1), a step of its
  proof plan, which the argument over an arbitrary base uses

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, §11, p. 53 (polarizations, their
  degree, principal polarizations, and the remark that this is not the same as $\lambda = \varphi_L$
  with $L$ on $A$, after Milne 1986, 13.2), and §8, pp. 34–40 ($\varphi_L$ and the sheaf
  $m^* L \otimes p^* L^{-1} \otimes q^* L^{-1}$).
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (10.12)
  (the dual abelian scheme $A^t$, after Mumford's *Geometric Invariant Theory*, 6.8; polarizations of
  abelian schemes, after Mumford's *Abelian Varieties*, p. 60, and *Geometric Invariant Theory*,
  Definition 6.3; symmetry of polarizations).
- G. van der Geer and B. Moonen, *Abelian Varieties*, book draft, Chapter VII, "Duality",
  <https://www.math.ru.nl/personal/bmoonen/BookAV/DualAV2.pdf>: Lemma (7.8), p. 100.
- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>: the
  discussion of polarizations of abelian schemes before Proposition 2.3.13, and Proposition 2.3.13,
  p. 16.
