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

    is exact, where $(1)$ is the twist by the Tate module $T_p(\mu) = \varprojlim_n \mu_{p^n}(C)$ of $\mathbb{G}_m$;

2. integrally, the cokernel of $\alpha_G \colon T \otimes_{\mathbb{Z}_p} \mathcal{O}_C \to (\operatorname{Lie} G^\vee)^\vee$ is killed by
   $p^{1/(p-1) + \varepsilon}$ for every $\varepsilon > 0$; more precisely, the sequence
   $0 \to (\operatorname{Lie} G)(1) \to T \otimes_{\mathbb{Z}_p} \mathcal{O}_C \to (\operatorname{Lie} G^\vee)^\vee \to 0$, with first map
   $\alpha_{G^\vee}^\vee(1)$ and second map $\alpha_G$, is a complex whose cohomology groups are killed by
   $p^{1/(p-1) + \varepsilon}$ for every $\varepsilon > 0$;
3. **kernel and annihilator.** Let $B \colon (T \otimes_{\mathbb{Z}_p} \mathcal{O}_C) \times (T_p G^\vee \otimes_{\mathbb{Z}_p} \mathcal{O}_C) \to \mathcal{O}_C(1)$
   be the $\mathcal{O}_C$-bilinear extension of the Weil pairing $T \times T_p G^\vee \to T_p(\mu)$ of Cartier duality. Then for
   $x \in T \otimes \mathcal{O}_C$,

    $$\alpha_G(x) = 0 \iff B(x, y) = 0 \text{ for every } y \in T_p G^\vee \otimes \mathcal{O}_C \text{ with } \alpha_{G^\vee}(y) = 0.$$

    This identity holds integrally, with no torsion bound, while the cokernel of $\alpha_G$ is controlled only by
    item 2. It follows from item 1. Under the Weil pairing, $\alpha_{G^\vee}^\vee(1)$ is the transpose of $\alpha_{G^\vee}$, so its
    image, which is $\ker(\alpha_G \otimes C)$ by exactness, is the annihilator of $\ker(\alpha_{G^\vee} \otimes C)$. Each
    kernel over $C$ is spanned by the integral kernel, and $(\operatorname{Lie} G^\vee)^\vee$ is torsion-free, so the two
    integral conditions agree.

## Depends on

- [p-divisible group](../../../../AlgebraicGeometry/abelian-varieties/deformations-and-p-divisible-groups/p-divisible-group.md), for $p$-divisible groups, their Serre duals and the Cartier duality between their finite levels
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for the twist $(1)$

## Proof depends on

- [p-divisible groups over the ring of integers of C](p-divisible-groups-over-o-c.md), for the Dieudonné theory over $\mathcal{O}_C/p$, the vector bundle $\mathcal{E}(G_0)$ and Proposition 5.1.1 on modifications of vector bundles (its items 1–3), and for its item 4: the modification $0 \to \mathcal{O}_X \otimes T \to \mathcal{E}(G_0) \to i_{\infty *}(\operatorname{Lie} G \otimes C) \to 0$ of Proposition 5.1.6 (i), the adjunction morphism inducing the quasi-logarithm on global sections (Proposition 5.1.6 (ii)) and, after a trivialisation of $\mathbb{Z}_p(1)$, the identification of the composite $(\mathcal{E}_{G^\vee})^\vee \to (\mathcal{F}_{G^\vee})^\vee \cong \mathcal{F}_G \to \mathcal{E}_G \cong (\mathcal{E}_{G^\vee})^\vee \otimes \mathcal{O}_X(1)$ with multiplication by $t$, which vanishes at $\infty$, from which Scholze–Weinstein reprove the exactness of item 1 after inverting $p$ (p. 51); item 3 follows from item 1; its classification by pairs $(T, W)$ (item 5) is built from the Hodge–Tate map and is not used

## Sources

- P. Scholze and J. Weinstein, "Moduli of p-divisible groups", Cambridge J. Math. 1 (2013), 145–237,
  arXiv:1211.6357 (version 2): Proposition 5.1.6 (ii)–(iii) (the map $\alpha_G$, its description through Cartier
  duality, and the exact sequence over $C$, with the first map $\alpha_{G^\vee}^\vee(1)$) and its proof ("Part (iii) is
  taken from [FGL08], Appendix C to Chapter 2", and, p. 51, "One could also reprove it using the machinery employed
  here", through part (i) and the identification of $f_G$ with multiplication by $t$; part (i) through Proposition 5.1.1); Proposition 4.3.6 and Remark 4.3.7, applied to $(T, T^+) = (C, \mathcal{O}_C)$ in the setting of
  §4.3 ("The cokernel of $T G(T^+) \otimes_{\mathbb{Z}_p} T^+ \to (\operatorname{Lie} G^\vee)^\vee$ is killed by $p^{1/(p-1)+\epsilon}$ for
  any $\epsilon > 0$. More precisely, there is a natural sequence [...] whose cohomology groups are killed by
  $p^{1/(p-1)+\epsilon}$", with first map $\alpha_{G^\vee}^\vee(1)$; the case $(C, \mathcal{O}_C)$ "is exactly [FGL08, Théorème II.1.1]", due to
  L. Fargues, in L. Fargues, A. Genestier, V. Lafforgue, *L'isomorphisme entre les tours de Lubin–Tate et de
  Drinfeld*, Progr. Math. 262, Birkhäuser, 2008).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses item 3, the identification of the kernel of the $\mathcal{O}_C$-linear Hodge–Tate map with the annihilator, under
  the Weil pairing, of the kernel of the dual map, as `GlobalTheory.CompanionTheory.Ar.HT.FarguesExact`, in its bound
  for a covolume.
