# Absolute prismatic site and prismatic F-crystals

This node is still to be broken down. It covers the absolute prismatic theory of Bhatt–Scholze from which they
prove the [classification of crystalline lattices by prismatic F-crystals](prismatic-f-crystals-and-crystalline-lattices.md),
and the results of Bhatt–Scholze 2019 that come after the
[crystalline comparison](crystalline-comparison-for-prismatic-cohomology.md) and on which that theory rests. For a
$p$-adic formal scheme $X$, the **absolute prismatic site** $X_\Delta$ is the opposite of the category of bounded
[prisms](prisms-and-prismatic-cohomology.md) $(A, I)$ with a map $\operatorname{Spf}(A/I) \to X$, with the topology
induced by the flat topology on prisms; it carries the structure sheaf $\mathcal{O}_\Delta$, $(A, I) \mapsto A$, with the
Frobenius $\varphi$ of the $\delta$-structures, and the ideal sheaf $I_\Delta \subset \mathcal{O}_\Delta$ of the Hodge–Tate
divisor, $(A, I) \mapsto I$. A **prismatic $F$-crystal** (of vector bundles) on $X$ is a vector bundle $\mathcal{E}$ on
$(X_\Delta, \mathcal{O}_\Delta)$ with an isomorphism
$\varphi_{\mathcal{E}} \colon (\varphi^* \mathcal{E})[1/I_\Delta] \cong \mathcal{E}[1/I_\Delta]$.

A good expansion has pages for:

1. the results of Bhatt–Scholze 2019 that come after the crystalline comparison and that the absolute theory
   uses: the Hodge–Tate comparison over a crystalline prism, deduced from the crystalline comparison and the
   Cartier isomorphism (Corollary 5.5); the Hodge–Tate and de Rham comparisons of §6 (Theorems 6.3 and 6.4); and the
   prismatic cohomology $\Delta_S$ of a quasiregular semiperfectoid
   ring $S$ and the conjugate filtration on its Hodge–Tate specialisation $\Delta_S/I$ (Theorem 1.14 (1),
   Construction 7.6; Proposition 7.10, whose proof uses the Hodge–Tate comparison), with the identification $\Delta_R \simeq A_{\mathrm{cris}}(R)$ for a quasiregular semiperfect
   $\mathbb{F}_p$-algebra $R$, which Bhatt–Scholze 2021 call the crystalline comparison for such $R$ (Example 4.7)
   and derive for $R = \mathcal{O}_C/p$ from Corollary 2.39 and Proposition 7.10, with
   $\Delta_{\mathcal{O}_C} = A_{\mathrm{inf}}$ (§5);
2. the absolute prismatic site, the quasi-syntomic and quasiregular semiperfectoid sites with their comparison
   with the prismatic site (Bhatt–Scholze 2021, Definition 2.3, §2, Proposition 2.14), $\mathbb{Z}_p$-local systems
   on the generic fibre through Laurent $F$-crystals (§3, Corollaries 3.7 and 3.8), and prismatic $F$-crystals
   (Definition 4.1) with their étale and crystalline realizations (Constructions 4.8 and 4.12), the latter through
   the identification of item 1 (Example 4.7);
3. Fargues's description of the prismatic $F$-crystals over $\mathcal{O}_C$ by pairs of a finite free
   $\mathbb{Z}_p$-module $T$ and a $B_{\mathrm{dR}}^+$-lattice in $T \otimes_{\mathbb{Z}_p} B_{\mathrm{dR}}$ (Theorem 5.2), of
   which Bhatt–Scholze use only the fully faithful direction (Theorem 5.2 and the end of Construction 5.5),
   whose proof they cite from Bhatt–Morrow–Scholze, Remark 4.29;
4. the descent machinery of §§6.1–6.3: the period sheaves on the quasiregular semiperfectoid site
   (Constructions 6.2 and 6.4); the $F$-crystal attached to a filtered $\varphi$-module $(D, \varphi_D, \operatorname{Fil}^*)$
   over $K$ on the "open unit disc" version of $\Delta_\bullet$ (Construction 6.5, Remark 6.6, Lemma 6.7), where, in
   Bhatt–Scholze's prismatic convention, the filtration is on $D \otimes_{W(k), \varphi} K$; and the boundedness of
   descent data at the boundary of the open unit disc (Propositions 6.8 and 6.10).

From this machinery Bhatt–Scholze prove the classification of prismatic $F$-crystals over $\mathcal{O}_K$
(Theorem 5.6), full faithfulness in §5 and essential surjectivity in §6.4, by descent along
$\operatorname{Spf}(\mathcal{O}_C) \to \operatorname{Spf}(\mathcal{O}_K)$; that classification is the result of
[prismatic F-crystals and lattices in crystalline representations](prismatic-f-crystals-and-crystalline-lattices.md)
and is not part of this node.

## Depends on

- [Prisms and prismatic cohomology](prisms-and-prismatic-cohomology.md), for bounded prisms, of which the absolute prismatic site is made, and the relative prismatic cohomology of item 1 (its items 1 and 2)
- [Crystalline representations](crystalline-representations.md), for $A_{\mathrm{cris}}$ and $B_{\mathrm{cris}}$, whose prismatic forms are among the period sheaves of items 1 and 4 (Bhatt–Scholze 2021, §5 and Construction 6.2)
- [de Rham representations](de-rham-representations.md), for $B_{\mathrm{dR}}^+$ and $B_{\mathrm{dR}}$ in Fargues's description of item 3 and the de Rham period sheaves of item 4 (Construction 6.4)
- [Weakly admissible filtered (φ, N)-modules](weakly-admissible-filtered-phi-n-modules.md), for the filtered $\varphi$-modules over $K$ (the case $N = 0$) of Construction 6.5 in item 4, whose filtration Bhatt–Scholze put on $D \otimes_{W(k), \varphi} K$ rather than on the base change $K \otimes_{K_0} D$ used on that page

## Proof depends on

- [Crystalline comparison for prismatic cohomology](crystalline-comparison-for-prismatic-cohomology.md), for the Hodge–Tate comparison over a crystalline prism deduced from it (Bhatt–Scholze 2019, Corollary 5.5), through which pass the Hodge–Tate comparison of Theorem 6.3 and the proof of Proposition 7.10 in item 1

## Expansion

A good expansion also states and links:

- $p$-adic formal schemes, for the absolute prismatic site and the étale realization of item 2, defined for any $p$-adic formal scheme (Bhatt–Scholze 2021, Definition 2.3 and Construction 4.8); the crystalline realization (Construction 4.12) is defined for quasi-syntomic ones
- the Cartier isomorphism (as used in Bhatt–Scholze 2019, Corollary 5.5), for the Hodge–Tate comparison over a crystalline prism in item 1
- the Beilinson fibre sequence of Antieau–Mathew–Morrow–Nikolaus (Bhatt–Scholze 2021, §1.1, citing [AMMN20], and §6.3, citing its Theorem 6.17), for the analytic continuation of Proposition 6.8 and the boundedness of descent data of Proposition 6.10 in item 4

## Sources

- B. Bhatt and P. Scholze, "Prisms and prismatic cohomology", Ann. of Math. 196 (2022), arXiv:1905.08229
  (version 4): Corollary 5.5 and §5 (introduction: "Using the Cartier isomorphism, we deduce the Hodge–Tate
  comparison over crystalline prisms (Corollary 5.5)"), Theorems 6.3 and 6.4, Theorem 1.14 and Proposition 7.10
  with its proof (pp. 59–60), Corollary 2.39.
- B. Bhatt and P. Scholze, "Prismatic F-crystals and crystalline Galois representations", Cambridge J. Math.
  11 (2023), 507–562, arXiv:2106.14735 (version 2): Definition 1.1 (= Definition 4.1), Definition 2.3,
  Proposition 2.14, Corollaries 3.7 and 3.8, Example 4.7, Constructions 4.8 and 4.12, §5 (Theorem 5.2, of which
  Bhatt–Scholze need "the easy direction": "For an elementary proof of full faithfulness (which is the only part we
  use), we refer to [BMS18, Remark 4.29]"; Construction 5.5), Constructions 6.2, 6.4 and 6.5, Remark 6.6, Lemma 6.7,
  Propositions 6.8 and 6.10, §1.1 (the outline of the proof of Theorem 5.6, with the Beilinson fibre sequence of
  [AMMN20]), §6.4 (proof of essential surjectivity), §§2–6.
