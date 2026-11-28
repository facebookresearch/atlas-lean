# Hahn series fields over an infinite field with a total residue map are undecidable

For an infinite field $k$ and a nontrivial ordered abelian group $\Gamma$, the Hahn series field $k((t^\Gamma))$ with the map picking out the constant coefficient has an undecidable theory, already its $\exists\forall$ part with a constant for $t$; the same holds for Puiseux series.

**Setting (Kartas).** For a field $k$ and an ordered abelian group $\Gamma$, the Hahn field $k((t^\Gamma))$ consists of the formal sums $f = \sum_{q \in \Gamma} c_q t^q$ with $c_q \in k$ and well-ordered support $\{q : c_q \neq 0\}$, valued by $v(f) = \min \operatorname{supp}(f)$; for $\Gamma = \mathbb{Z}$ it is the Laurent series field $k((t))$. The *total residue map* $\operatorname{res} : k((t^\Gamma)) \to k$ sends $f$ to its constant coefficient $c_0$; it is $k$-linear and extends the residue map of the valuation ring. $L_{\mathrm{res}}$ is the three-sorted language $L_{\mathrm{val}}$ of valued fields (sorts for the field, the value group and the residue field, with the valuation $v$) together with a function symbol for $\operatorname{res}$, and $L_{\mathrm{res},t}$ adds a constant for $t = t^1$, for a fixed positive element $1 \in \Gamma$. The Puiseux series field is $k\{\{t\}\} = \bigcup_{n} k((t^{1/n}))$.

**Theorem (Kartas).** Let $k$ be an infinite field and $\Gamma$ a nontrivial ordered abelian group. Then the $\exists\forall$-theory of $(k((t^\Gamma)), \operatorname{res})$ in $L_{\mathrm{res},t}$ is undecidable, and so is that of the Puiseux series field $k\{\{t\}\}$ (Theorem B in Subsection 2.2.1 of arXiv:2203.02374v2).

If $\Gamma$ has rank $1$, the same paper shows more: $(k((t^\Gamma)), \operatorname{res})$ interprets $(\mathbb{N}, +, \cdot)$ without parameters, so $k((t^\Gamma))$ is undecidable in $L_{\mathrm{res}}$, without the constant for $t$; the same holds for $k\{\{t\}\}$ (Theorem C in Subsection 2.3 of arXiv:2203.02374v2). In particular $k((t))$ is undecidable in $L_{\mathrm{res}}$ for every infinite field $k$, and $\mathbb{C}((t))$ is $\exists\forall$-undecidable with the complex residue at $0$ and a constant for $t$ (Corollary 2.2.5). The proof uses that $k$ is infinite; the case of a finite field $k$, where $\operatorname{res}$ is definable in the language of rings with a parameter for $t$ (Becker, Denef and Lipshitz), is not covered. The same paper shows that the theory of valued fields with a total residue map and a lift of the residue field has no model companion.

## Depends on

- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The subfield $k$ is defined without parameters as the set of $x$ with $\operatorname{res}(xy) = \operatorname{res}(x)\operatorname{res}(y)$ for all $y$. For $a = \sum c_q t^q$ let $p_a(X) = \sum_{n \ge 0} c_{-n} X^n \in k[X]$; then $\operatorname{res}\!\left(\frac{a}{1 - ty}\right) = p_a(y)$ for $y \in k$. Since $k$ is infinite, a polynomial vanishes identically exactly when it vanishes on all of $k$, so a system of polynomial equations with coefficients in $\mathbb{Z}[T]$ has a solution in $k[T]$ exactly when an $\exists\forall$ sentence of $L_{\mathrm{res},t}$ holds in $k((t^\Gamma))$. Denef's theorem that Hilbert's tenth problem over $k[T]$ with coefficients in $\mathbb{Z}[T]$ is undecidable for every field $k$ gives the theorem. For the rank-one strengthening the weak monadic second-order theory of $k$ is interpreted, and with it arithmetic. A complete expansion links pages for Denef's undecidability of Hilbert's tenth problem over polynomial rings $k[T]$ and for the interpretation of arithmetic in weak monadic second-order logic over an infinite field.

## Sources

- K. Kartas, "Valued fields with a total residue map", *Journal of Mathematical Logic* 24(3), 2024, article 2450005, doi:[10.1142/S0219061324500053](https://doi.org/10.1142/S0219061324500053); read as arXiv:2203.02374v2 ([arXiv](https://arxiv.org/abs/2203.02374v2)), whose labels are used: Theorems A and B of the introduction, Lemma 2.1.1, Theorem B in Subsection 2.2.1 (the general form of the introduction's Theorem B), Corollary 2.2.5, and Theorem C with Lemmas 2.3.3 and 2.3.4 in Subsection 2.3.
