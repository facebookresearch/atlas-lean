# Prisms and prismatic cohomology

This node is still to be broken down. It covers the definitions and the general machinery of Bhatt–Scholze's
prismatic cohomology from which they prove the
[crystalline comparison](crystalline-comparison-for-prismatic-cohomology.md); the absolute prismatic theory,
which comes after the crystalline comparison, is the node on the
[absolute prismatic site and prismatic F-crystals](absolute-prismatic-site-and-prismatic-f-crystals.md). A
**$\delta$-ring** is a commutative ring $A$ with a map of sets $\delta \colon A \to A$ such that
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
   crystalline cohomology of $X$ over a crystalline prism (§5).

The crystalline comparison (Bhatt–Scholze 2019, Theorem 5.2), proved from items 1 and 2, is the result of
[crystalline comparison for prismatic cohomology](crystalline-comparison-for-prismatic-cohomology.md) and is not part
of this node. The results deduced from it (Corollary 5.5, Theorems 6.3 and 6.4), the prismatic cohomology of
quasiregular semiperfectoid rings and the absolute prismatic theory belong to the node on the
[absolute prismatic site and prismatic F-crystals](absolute-prismatic-site-and-prismatic-f-crystals.md).

## Depends on

Its statement uses the inputs listed under Expansion.

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

A good expansion also states and links:

- derived completeness of modules (Bhatt–Scholze 2019, §1.2), for the derived $(p, I)$-completeness in the definition of a prism
- smooth $p$-adic formal schemes over $A/I$ (Bhatt–Scholze 2019, Definition 4.1 and §4), for the relative prismatic site of item 2

## Sources

- B. Bhatt and P. Scholze, "Prisms and prismatic cohomology", Ann. of Math. 196 (2022), arXiv:1905.08229
  (version 4): Definition 2.1 and Remark 2.2 ($\delta$-rings and Frobenius lifts), Example 2.6 (the initial
  $\delta$-ring) and Example 2.20 (1) ($\delta(p) = 1 - p^{p-1}$), Definition 3.2 (prisms, with
  derived $(p, I)$-completeness), Lemma 3.7 (1) (bounded prisms are classically $(p, I)$-complete), Example 1.3,
  Corollary 2.39, Theorem 1.8 with Theorems 5.2, 6.3 and 6.4, §5 (introduction: "the key tool is the relationship
  between divided power envelopes and $\delta$-structures (Corollary 2.39). Using the Cartier isomorphism, we deduce
  the Hodge–Tate comparison over crystalline prisms (Corollary 5.5)"), §§2–6.
