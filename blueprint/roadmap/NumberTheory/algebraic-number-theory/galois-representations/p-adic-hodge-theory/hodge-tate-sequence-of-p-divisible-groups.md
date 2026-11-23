# Hodge–Tate sequence of a p-divisible group

Let $C$ be a complete algebraically closed nonarchimedean field extension of $\mathbb{Q}_p$ with ring of integers
$\mathcal{O}_C$, let $G$ be a $p$-divisible group over $\mathcal{O}_C$ with Serre dual $G^\vee$, let
$T = T_p G = \varprojlim_n G[p^n](\mathcal{O}_C)$ be its Tate module and $\operatorname{Lie} G$ its Lie algebra, a
finite free $\mathcal{O}_C$-module. The map $\mathbb{Q}_p/\mathbb{Z}_p \otimes_{\mathbb{Z}_p} T \to G$ induces by Cartier
duality $G^\vee \to \mu_{p^\infty} \otimes_{\mathbb{Z}_p} T^\vee$, and on Lie algebras
$\operatorname{Lie} G^\vee \to T^\vee \otimes_{\mathbb{Z}_p} \mathcal{O}_C$; dualizing gives the **Hodge–Tate map**
$\alpha_G \colon T \otimes_{\mathbb{Z}_p} \mathcal{O}_C \to (\operatorname{Lie} G^\vee)^\vee$. Then:

1. after inverting $p$, the sequence
   $$0 \to \operatorname{Lie} G \otimes_{\mathcal{O}_C} C(1) \xrightarrow{\ \alpha_{G^\vee}^\vee(1)\ } T \otimes_{\mathbb{Z}_p} C \xrightarrow{\ \alpha_G\ } (\operatorname{Lie} G^\vee \otimes_{\mathcal{O}_C} C)^\vee \to 0$$
   is exact, where $(1)$ is the Tate twist by $\mathbb{Z}_p(1) = T_p \mu_{p^\infty}$;
2. integrally, $0 \to (\operatorname{Lie} G)(1) \to T \otimes_{\mathbb{Z}_p} \mathcal{O}_C \to (\operatorname{Lie} G^\vee)^\vee \to 0$
   is a complex whose cohomology groups are killed by $p^{1/(p-1) + \varepsilon}$ for every $\varepsilon > 0$; in
   particular the cokernel of $\alpha_G$ is.

## Depends on

- [p-divisible group](../../../../AlgebraicGeometry/abelian-varieties/deformations-and-p-divisible-groups/p-divisible-group.md), for $p$-divisible groups, their Serre duals and the Cartier duality between their finite levels
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for the twist $(1)$

## Proof depends on

- [p-divisible groups over the ring of integers of C](p-divisible-groups-over-o-c.md), for the Dieudonné theory over $A_{\mathrm{cris}}$, the classification of $p$-divisible groups over $\mathcal{O}_C$ and the vector bundles on the Fargues–Fontaine curve used in the proof, and for Fargues's original proof of the integral statement

## Sources

- P. Scholze and J. Weinstein, "Moduli of p-divisible groups", Cambridge J. Math. 1 (2013), 145–237,
  arXiv:1211.6357 (version 2): Proposition 5.1.6 (ii)–(iii) (the map $\alpha_G$, its description through Cartier
  duality, and the exact sequence over $C$); Proposition 4.3.6 and Remark 4.3.7 (the integral sequence over a
  perfectoid affinoid $(T, T^+)$, whose case $(C, \mathcal{O}_C)$ "is exactly [FGL08, Théorème II.1.1]", due to
  L. Fargues, in L. Fargues, A. Genestier, V. Lafforgue, *L'isomorphisme entre les tours de Lubin–Tate et de
  Drinfeld*, Progr. Math. 262, Birkhäuser, 2008).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses a consequence, the identification of the kernel of the $\mathcal{O}_C$-linear Hodge–Tate map with the
  annihilator, under the Weil pairing, of the kernel of the dual map, as
  `GlobalTheory.CompanionTheory.Ar.HT.FarguesExact`, in its bound for a covolume.
