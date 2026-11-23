# Prisms and prismatic cohomology

This node is still to be broken down. It covers the definitions and the general machinery of Bhatt–Scholze's
prismatic cohomology that the [crystalline comparison](crystalline-comparison-for-prismatic-cohomology.md) and
the [classification of crystalline lattices by prismatic F-crystals](prismatic-f-crystals-and-crystalline-lattices.md)
use. A **prism** is a pair $(A, I)$ of a $\delta$-ring $A$ (a ring with a map $\delta$ making
$\varphi_A(x) = x^p + p\delta(x)$ a ring endomorphism lifting Frobenius) and an ideal $I$ defining a Cartier divisor
of $\operatorname{Spec} A$, such that $A$ is $(p, I)$-adically complete and $p \in I + \varphi_A(I) A$; it is
**bounded** if $A/I$ has bounded $p^\infty$-torsion, and **crystalline** if $I = (p)$.

A good expansion has pages for:

1. $\delta$-rings and prisms, with the crystalline, perfect and Breuil–Kisin examples (Bhatt–Scholze 2019,
   Definition 1.1, Remark 1.2, Example 1.3, §§2–3, Theorem 3.10);
2. the relative prismatic site $(X/A)_\Delta$ of a smooth $p$-adic formal scheme $X$ over $A/I$, its structure
   sheaf and prismatic cohomology $R\Gamma_\Delta(X/A)$ with its $\varphi_A$-linear Frobenius (§4), and the
   crystalline cohomology $R\Gamma_{\mathrm{crys}}(X/A)$ of $X$ over a crystalline prism (§5);
3. the proof of the crystalline comparison, through the Hodge–Tate comparison and the de Rham comparison
   (Theorem 1.8 (1)–(3) with Theorems 5.2, 6.3 and 6.4);
4. the absolute prismatic site $(Y)_\Delta$ of a $p$-adic formal scheme with $\mathcal{O}_\Delta$, $I_\Delta$ and
   $\varphi$, the quasi-syntomic site, the étale and crystalline realizations of prismatic $F$-crystals, and the
   proof of their classification over $\mathcal{O}_K$ by quasi-syntomic descent, through Breuil–Kisin modules and
   Kedlaya's slope filtrations (Bhatt–Scholze 2021, §§2–6, Construction 4.8, Construction 4.12, Theorem 5.6).

## Sources

- B. Bhatt and P. Scholze, "Prisms and prismatic cohomology", Ann. of Math. 196 (2022), arXiv:1905.08229
  (version 4): Definition 1.1, Remark 1.2, Example 1.3, Theorem 1.8 with the theorems it cites, §§2–6.
- B. Bhatt and P. Scholze, "Prismatic F-crystals and crystalline Galois representations", Cambridge J. Math.
  11 (2023), 507–562, arXiv:2106.14735 (version 2): Definition 1.1 (= Definition 4.1), Constructions 4.8 and 4.12,
  §§2–6, and the outline of the proof of Theorem 5.6 in §1.1.
