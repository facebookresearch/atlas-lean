# Loewe additivity consistency condition

Let two compounds have dose–response curves $f_1, f_2 : \mathbb{R}_{\ge 0} \to \mathbb{R}$ that are continuous and strictly monotone, start from the same response at zero dose and converge to the same maximal response as dose tends to infinity, so that every dose of one compound has a **response-equivalent dose** of the other:

$$x_1^{\mathrm{equiv}}(x_2) = f_1^{-1}\big(f_2(x_2)\big), \qquad x_2^{\mathrm{equiv}}(x_1) = f_2^{-1}\big(f_1(x_1)\big).$$

Replacing one dose by its equivalent in the other compound defines two explicit Loewe-additive null response surfaces

$$f_{2\to1}(x_1,x_2) = f_1\big(x_1 + f_1^{-1}(f_2(x_2))\big), \qquad f_{1\to2}(x_1,x_2) = f_2\big(f_2^{-1}(f_1(x_1)) + x_2\big).$$

The **Loewe additivity consistency condition** (LACC) requires that the exchange direction be irrelevant:

$$f_{2\to1}(x_1,x_2) = f_{1\to2}(x_1,x_2) \qquad \text{for all } x_1, x_2 \ge 0.$$

**Theorem.** The LACC holds if and only if a dose and its equivalent are proportional: there is a constant $c > 0$ with

$$f_1^{-1}\big(f_2(x_2)\big) = c\, x_2, \qquad f_2^{-1}\big(f_1(x_1)\big) = x_1 / c .$$

Equivalently, $\log x_1^{\mathrm{equiv}}(x_2) = \log c + \log x_2$: the two curves are horizontal shifts of each other on the log-dose axis. For Hill curves $f(x) = y_\infty + (y_0 - y_\infty)/(1 + (x/e)^s)$ this means equal baseline $y_0$, equal maximal effect $y_\infty$ and equal slope $s$, with only the half-maximal dose $e$ differing.

**Corollary.** If the LACC holds, then the implicit general isobole surface $f_{\mathrm{GI}}$ (defined by $x_1/X_1(y) + x_2/X_2(y) = 1$ with $X_j = f_j^{-1}$) coincides with $f_{2\to1} = f_{1\to2}$, and all isoboles are parallel straight lines.

## Expansion

If $x_1^{\mathrm{equiv}}(x_2) = c x_2$, both surfaces equal $f_1(x_1 + c x_2) = f_2(x_1/c + x_2)$, and the isobole at response $y$ is the line $x_1 + c x_2 = X_1(y)$. Conversely, the supplementary proof shows that requiring the two surfaces to agree for every dose pair forces the monotone equivalence map to be linear through the origin. Since real compounds rarely have shifted-copy curves, the general isobole equation is usually internally inconsistent; the paper therefore proposes explicit, consistent alternatives (such as averaging $f_{2\to1}$ and $f_{1\to2}$) as null reference models for synergy scoring.

## Sources

- S. Lederer, T. M. H. Dijkstra and T. Heskes, "Additive dose response models: explicit formulation and the Loewe additivity consistency condition", Frontiers in Pharmacology 9 (2018), 31, Section 2.2, Eqs. (4)–(11), Theorem 1 and Corollary 1, <https://doi.org/10.3389/fphar.2018.00031>, PMCID: PMC5808155.
- S. Loewe, "The problem of synergism and antagonism of combined drugs", Arzneimittelforschung 3 (1953), 285–290.
