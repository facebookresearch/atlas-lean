# Prisms and prismatic cohomology

This node is still to be broken down. It covers the definitions and the general machinery of Bhatt–Scholze's
prismatic cohomology that the [crystalline comparison](crystalline-comparison-for-prismatic-cohomology.md) and
the [classification of crystalline lattices by prismatic F-crystals](prismatic-f-crystals-and-crystalline-lattices.md)
use. A **$\delta$-ring** is a commutative ring $A$ with a map of sets $\delta \colon A \to A$ such that
$\delta(0) = \delta(1) = 0$ and, for all $x, y \in A$,

$$\delta(xy) = x^p \delta(y) + y^p \delta(x) + p \, \delta(x) \delta(y), \qquad
\delta(x + y) = \delta(x) + \delta(y) + \frac{x^p + y^p - (x + y)^p}{p},$$

the last fraction meaning the integer polynomial $-\sum_{0 < i < p} \frac{1}{p}\binom{p}{i} x^i y^{p-i}$. Then
$\varphi_A(x) = x^p + p \delta(x)$ is a ring endomorphism lifting the Frobenius of $A/p$; when $A$ is $p$-torsion-free,
every Frobenius lift comes from a unique $\delta$-structure, but in general a Frobenius lift need not come from any:
in every $\delta$-ring $\delta(p) = 1 - p^{p-1}$, its value in the initial $\delta$-ring, so a nonzero ring in which
$p = 0$ (such as $\mathbb{F}_p[[t]]$, whose Frobenius lifts itself) carries no $\delta$-structure, since there
$\delta(p) = \delta(0) = 0$ would equal $1$. A **prism** is a $\delta$-ring $A$ with an ideal $I$ defining a Cartier divisor on
$\operatorname{Spec} A$ such that $A$ is **derived** $(p, I)$-complete and $p \in I + \varphi_A(I) A$. It is
**bounded** if $A/I$ has bounded $p^\infty$-torsion, in which case $A$ is also classically $(p, I)$-complete, and
**crystalline** if $I = (p)$.

A good expansion has pages for:

1. $\delta$-rings and prisms, with the crystalline, perfect and Breuil–Kisin examples (Bhatt–Scholze 2019,
   Definition 2.1, Remark 2.2, Definition 3.2, Lemma 3.7 (1), Example 1.3, §§2–3, Theorem 3.10), and the comparison
   between divided power envelopes and $\delta$-envelopes (Corollary 2.39);
2. the relative prismatic site $(X/A)_\Delta$ of a smooth $p$-adic formal scheme $X$ over $A/I$, its structure
   sheaf and prismatic cohomology $R\Gamma_\Delta(X/A)$ with its $\varphi_A$-linear Frobenius (§4), and the
   crystalline cohomology of $X$ over a crystalline prism (§5);
3. the absolute prismatic site of a $p$-adic formal scheme with $\mathcal{O}_\Delta$, $I_\Delta$ and $\varphi$, the quasi-syntomic
   and quasiregular semiperfectoid sites with their comparison with the prismatic site (Bhatt–Scholze 2021, §2,
   Proposition 2.14), $\mathbb{Z}_p$-local systems on the generic fibre through Laurent $F$-crystals (§3, Corollaries 3.7
   and 3.8), and prismatic $F$-crystals with their étale and crystalline realizations (§4, Constructions 4.8 and 4.12),
   the latter through the identification $\Delta_R \simeq A_{\mathrm{cris}}(R)$ for quasiregular semiperfect
   $\mathbb{F}_p$-algebras $R$ (Example 4.7; for $R = \mathcal{O}_C/p$, §5, from Bhatt–Scholze 2019, Corollary 2.39 and
   Proposition 7.10); Fargues's description of the prismatic $F$-crystals over $\mathcal{O}_C$ by pairs of a finite free
   $\mathbb{Z}_p$-module $T$ and a $B_{\mathrm{dR}}^+$-lattice in $T \otimes B_{\mathrm{dR}}$ (Theorem 5.2, whose full faithfulness
   Bhatt–Scholze cite from Bhatt–Morrow–Scholze, Remark 4.29); and the descent machinery of §§6.1–6.3: the period
   sheaves on the quasiregular semiperfectoid site (Constructions 6.2 and 6.4), the $F$-crystal attached to a filtered
   $\varphi$-module over $K$ on the "open unit disc" version of $\Delta_\bullet$ (Construction 6.5, Remark 6.6, Lemma 6.7),
   and the boundedness of descent data at the boundary of the open unit disc (Propositions 6.8 and 6.10). From this
   machinery Bhatt–Scholze prove the classification of prismatic $F$-crystals over $\mathcal{O}_K$ (Theorem 5.6),
   full faithfulness in §5 and essential surjectivity in §6.4, by descent along
   $\operatorname{Spf}(\mathcal{O}_C) \to \operatorname{Spf}(\mathcal{O}_K)$; that classification is the result of
   [prismatic F-crystals and lattices in crystalline representations](prismatic-f-crystals-and-crystalline-lattices.md)
   and is not part of this node, nor is the crystalline comparison (Bhatt–Scholze 2019, Theorem 5.2), the result of
   [crystalline comparison for prismatic cohomology](crystalline-comparison-for-prismatic-cohomology.md), whose proof
   uses items 1 and 2; nor are the Hodge–Tate comparison over a crystalline prism (Bhatt–Scholze 2019, Corollary 5.5) and
   the mixed characteristic Hodge–Tate and de Rham comparisons (Theorems 6.3 and 6.4), which Bhatt–Scholze deduce from
   the crystalline comparison.

## Depends on

- [Crystalline representations](crystalline-representations.md), for $A_{\mathrm{cris}}$ and $B_{\mathrm{cris}}$, whose prismatic forms are among the period sheaves of item 3 (Bhatt–Scholze 2021, §5 and Construction 6.2)
- [de Rham representations](de-rham-representations.md), for $B_{\mathrm{dR}}^+$ and $B_{\mathrm{dR}}$ in Fargues's description and the de Rham period sheaves of item 3 (Construction 6.4)
- [Weakly admissible filtered (φ, N)-modules](weakly-admissible-filtered-phi-n-modules.md), for the filtered $\varphi$-modules over $K$ (the case $N = 0$) of Construction 6.5 in item 3

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

A good expansion also states and links:

- derived completeness of modules (Bhatt–Scholze 2019, §1.2), for the derived $(p, I)$-completeness in the definition of a prism
- smooth $p$-adic formal schemes over $A/I$ (Bhatt–Scholze 2019, Definition 4.1 and §4), for the relative prismatic site of item 2
- $p$-adic formal schemes, for the absolute prismatic site and the étale realization of item 3, defined for any $p$-adic formal scheme (Bhatt–Scholze 2021, Definition 2.3 and Construction 4.8); the crystalline realization (Construction 4.12) is defined for quasi-syntomic ones
- the Beilinson fibre sequence of Antieau–Mathew–Morrow–Nikolaus (Bhatt–Scholze 2021, §1.1, citing [AMMN20], and §6.3, citing its Theorem 6.17), for the analytic continuation of Proposition 6.8 and the boundedness of descent data of Proposition 6.10 in item 3

## Sources

- B. Bhatt and P. Scholze, "Prisms and prismatic cohomology", Ann. of Math. 196 (2022), arXiv:1905.08229
  (version 4): Definition 2.1 and Remark 2.2 ($\delta$-rings and Frobenius lifts), Example 2.6 (the initial
  $\delta$-ring) and Example 2.20 (1) ($\delta(p) = 1 - p^{p-1}$), Definition 3.2 (prisms, with
  derived $(p, I)$-completeness), Lemma 3.7 (1) (bounded prisms are classically $(p, I)$-complete), Example 1.3,
  Corollary 2.39, Theorem 1.8 with Theorems 5.2, 6.3 and 6.4, §5 (introduction: "the key tool is the relationship
  between divided power envelopes and $\delta$-structures (Corollary 2.39). Using the Cartier isomorphism, we deduce
  the Hodge–Tate comparison over crystalline prisms (Corollary 5.5)"), §§2–6.
- B. Bhatt and P. Scholze, "Prismatic F-crystals and crystalline Galois representations", Cambridge J. Math.
  11 (2023), 507–562, arXiv:2106.14735 (version 2): Definition 1.1 (= Definition 4.1), Constructions 4.8 and 4.12,
  §1.1 (the outline of the proof of Theorem 5.6, with the Beilinson fibre sequence of [AMMN20]), §6.4 (proof of
  essential surjectivity), §§2–6.
