# Zarhin's trick for abelian schemes

This node is still to be broken down. It covers the relative forms of
[Zarhin's trick](zarhin-trick.md) for an [abelian scheme](abelian-scheme.md) $A$ over a base $S$,
with [dual abelian scheme](dual-abelian-scheme.md) $A^t$. The targets are:

1. (Moret-Bailly, after Deligne.) To every abelian scheme $A$ over a scheme $S$ with a
   [polarization](polarization.md) $\varphi \colon A \to A^t$ one can attach, canonically and
   compatibly with every base change, a principal polarization of $(A \times_S A^t)^4$.
2. (The form used by Alpöge's library.) Let $C$ be an algebraically closed field, $v \colon C \to
   \mathbb{R}_{\ge 0}$ a valuation with real values, hence of rank at most one, and $R = \{v \le
   1\}$ its valuation ring; let $A$ be an abelian scheme over $R$ and $L$ a relatively ample line
   bundle on $A$. Then there are a principally polarized abelian scheme $P$ over $R$, its principal
   polarization being induced by a **symmetric** line bundle $M$ on $P$, and homomorphisms $i \colon
   A \to P$ and $r \colon P \to A$ with $r \circ i = \mathrm{id}_A$.

Moret-Bailly proves 1 for every base: with the abelian schemes $A \otimes_\mathbb{Z} M$ for a free
$\mathbb{Z}$-module $M$ of finite type and the isomorphism $(A \otimes M)^t \cong A^t \otimes M^*$
compatible with biduality (IX, 1.2), the polarizations $\varphi \otimes B$ for a symmetric positive
definite bilinear form $B$ on $M$ and their degrees (IX, 1.3), and the descent of polarizations
along isogenies through finite flat subgroup schemes and Weil pairings. Descent along an isotropic
subgroup does not by itself reach degree one: IX, 1.4–1.6 (pp. 206–208) construct the isotropic
subgroup and a positive definite unimodular form on a quaternionic lattice with the divisibility
required, through a representation of an integer as a sum of four squares.

Target 2 asks for more than 1 gives. Its proof needs, besides 1: the relative theorem of the cube
over $R$, to make the Mumford bundle $\Lambda(L)$ additive and the morphism $A \to A^t$ that
classifies it a homomorphism, the polarization $\varphi_L$ (a cube theorem over a field does not
give the relative one by base change); and a symmetric line bundle inducing the principal
polarization of $P = (A \times_R A^t)^4$. An ample line bundle inducing a principal polarization
need not be symmetric: on an elliptic curve $E$ the bundle $\mathcal{O}_E([x])$ induces the
principal polarization for every point $x$, but is symmetric only when $2x = 0$. A good expansion
has pages for the steps of 1 above; for the relative theorem of the cube for abelian schemes over
$R$; and for the existence over $R$ of a symmetric line bundle inducing a given principal
polarization, a bridge for which no source has yet been identified.

## Depends on

- [Dual abelian scheme](dual-abelian-scheme.md)
- [Polarization](polarization.md), for polarizations of abelian schemes
- [Theorem of the cube, theorem of the square and the seesaw principle](theorem-of-the-cube.md), for
  the Mumford bundle over a field; 2 needs its relative form over $R$, a page of the expansion

## Proof depends on

- [Dual abelian scheme](dual-abelian-scheme.md), for the dual abelian scheme and dual homomorphisms
  over $S$, from which $(A \otimes M)^t \cong A^t \otimes M^*$ follows (Moret-Bailly, IX, 1.2)
- [Lagrange's four-square theorem](../../NumberTheory/quadratic-forms-sums-of-squares/sums-of-squares/lagrange-four-square-theorem.md),
  for the representation of an integer as a sum of four squares in Moret-Bailly's IX, 1.4–1.6

The theorem over a field of Zarhin's trick is the case of a point, not a step of these two proofs.

## Sources

- L. Moret-Bailly, *Pinceaux de variétés abéliennes*, Astérisque 129, 1985,
  <https://www.numdam.org/item/AST_1985__129__1_0/>: Chapter IX, §1, Lemme 1.1 ("un lemme de
  Zarhin", with a proof inspired by notes of P. Deligne), 1.2–1.3 and 1.4–1.6, pp. 205–208.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 2 as `GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement`, for a valuation `Valuation C
  NNReal` and its ring of integers, and derives it from the existence of dual abelian schemes, the
  relative theorem of the cube, a quasi-inverse construction of the principal polarization and the
  step `SymB.symmetricBundle`, which supplies the symmetric line bundle required by its principally
  polarized abelian schemes (`zarhinStatement_of_dual_cube_qiR`).
