# Zarhin's trick for abelian schemes

This node is still to be broken down. It covers the relative forms of [Zarhin's trick](zarhin-trick.md)
for an [abelian scheme](abelian-scheme.md) $A$ over a base $S$, with
[dual abelian scheme](dual-abelian-scheme.md) $A^t$. The targets are:

1. (Moret-Bailly, after Deligne.) To every abelian scheme $A$ over a scheme $S$ with a
   [polarization](polarization.md) $\varphi \colon A \to A^t$ one can attach, canonically and compatibly
   with every base change, a principal polarization of $(A \times_S A^t)^4$.
2. (The form used by Alpöge's library.) Let $C$ be an algebraically closed field with a valuation and
   $R$ its valuation ring, $A$ an abelian scheme over $R$ and $L$ a relatively ample invertible sheaf on
   $A$. Then there are a principally polarized abelian scheme $P$ over $R$, with a polarizing line
   bundle, and homomorphisms $i \colon A \to P$ and $r \colon P \to A$ with $r \circ i = \mathrm{id}_A$.

Moret-Bailly proves 1 for every base. Target 2 asks for more than 1 gives: the polarization
$\varphi_L$ attached to $L$, the principal polarization of $P = (A \times_R A^t)^4$ from 1, the inclusion
$i$ of $A$ as a factor and the projection $r$, and a line bundle on $P$ that induces the principal
polarization, which over a general base a polarization need not have. A good expansion has pages
for: the abelian schemes $A \otimes_\mathbb{Z} M$ for a free $\mathbb{Z}$-module $M$ of finite type, the
isomorphism $(A \otimes M)^t \cong A^t \otimes M^*$ and its compatibility with biduality (Moret-Bailly,
IX, 1.2); the polarizations $\varphi \otimes B$ for a symmetric positive definite bilinear form $B$
on $M$, and their degrees (IX, 1.3); the descent of polarizations along isogenies of abelian schemes,
through finite flat subgroup schemes and Weil pairings, which completes the proof of 1; and, for 2,
the polarization $\varphi_L$ of a relatively ample $L$ and the existence of a polarizing line bundle for
the principal polarization of 1 over the valuation ring $R$, a bridge for which no source has yet been
identified.

## Depends on

- [Zarhin's trick](zarhin-trick.md)
- [Dual abelian scheme](dual-abelian-scheme.md)
- [Polarization](polarization.md), for polarizations of abelian schemes

## Sources

- L. Moret-Bailly, *Pinceaux de variétés abéliennes*, Astérisque 129, 1985,
  <https://www.numdam.org/item/AST_1985__129__1_0/>: Chapter IX, §1, Lemme 1.1 ("un lemme de Zarhin",
  with a proof inspired by notes of P. Deligne) and 1.2–1.3, p. 205 and following.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) states 2 as
  `GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement`, and derives it from the existence of dual
  abelian schemes, the theorem of the cube and a further step on symmetric line bundles
  (`zarhinStatement_of_dual_cube`).
