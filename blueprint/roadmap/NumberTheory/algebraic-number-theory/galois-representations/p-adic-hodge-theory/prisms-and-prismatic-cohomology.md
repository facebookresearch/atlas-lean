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
3. the proof of the crystalline comparison (Theorem 5.2) from Corollary 2.39; the Hodge–Tate comparison over a
   crystalline prism, deduced from the crystalline comparison and the Cartier isomorphism (Corollary 5.5); and the
   mixed characteristic Hodge–Tate comparison and the de Rham comparison of §6 (Theorems 6.3 and 6.4), whose proofs
   use the crystalline case;
4. the absolute prismatic site of a $p$-adic formal scheme with $\mathcal{O}_\Delta$, $I_\Delta$ and $\varphi$, the
   quasi-syntomic site, the étale and crystalline realizations of prismatic $F$-crystals, and the proof of their
   classification over $\mathcal{O}_K$ (Bhatt–Scholze 2021, §§2–6, Constructions 4.8 and 4.12, Theorem 5.6) by
   quasi-syntomic descent along $\operatorname{Spf}(\mathcal{O}_C) \to \operatorname{Spf}(\mathcal{O}_K)$. Its inputs are the
   construction of the $F$-crystal over $\mathcal{O}_C$ following Kisin, through Kedlaya's slope filtrations as
   observed by Berger; the Beilinson fibre sequence of Antieau–Mathew–Morrow–Nikolaus, used to build the descent
   isomorphism (Bhatt–Scholze 2021, §1.1); and, in the proof of essential surjectivity (§6.4), the weak admissibility
   of the filtered $\varphi$-module of the given crystalline representation together with the vector bundles on the
   Fargues–Fontaine curve ([FF19] Corollary 11.2.22, Proposition 10.5.6, Theorem 8.2.10 (1); [SW18] Theorem 14.2.1).

## Depends on

- [Crystalline representations](crystalline-representations.md), for the lattices in crystalline representations of $G_K$ given by the étale realization of item 4
- Not yet a page: derived completeness of modules, for the derived $(p, I)$-completeness in the definition of a prism
- Not yet a page: smooth $p$-adic formal schemes over $A/I$, for the relative prismatic site of item 2
- Not yet a page: $p$-adic formal schemes, for the absolute prismatic site and the étale realization of item 4, defined for any $p$-adic formal scheme (Bhatt–Scholze 2021, Definition 2.3 and Construction 4.8); the crystalline realization (Construction 4.12) is defined for quasi-syntomic ones

## Proof depends on

- [Weakly admissible implies admissible](colmez-fontaine-theorem.md), for Fontaine's theorem that $D_{\mathrm{cris}}$ of a crystalline representation is weakly admissible, used in item 4
- [p-divisible groups over the ring of integers of C](p-divisible-groups-over-o-c.md), for the Fargues–Fontaine curve and its vector bundles, used in item 4
- Not yet a page: Bhatt–Scholze's construction of the $F$-crystal over $\mathcal{O}_C$, an $A_{\mathrm{inf}}$-variant of Kisin's argument (Bhatt–Scholze 2021, §1.1 and §6.4, n. 12), which rests on Kedlaya's slope filtration theorem through Berger's observation, for item 4
- Not yet a page: the Beilinson fibre sequence of Antieau–Mathew–Morrow–Nikolaus, for the descent isomorphism of item 4
- Not yet a page: the Cartier isomorphism, for the Hodge–Tate comparison over a crystalline prism in item 3

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
