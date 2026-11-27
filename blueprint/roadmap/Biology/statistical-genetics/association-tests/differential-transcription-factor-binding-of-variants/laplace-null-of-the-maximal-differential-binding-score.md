# Laplace null of the maximal differential binding score

For a transcription-factor model $M$ of length $m$ and a single-nucleotide variant, let $W$ and $Z$ be the binding-score $p$-values of a length-$m$ subsequence carrying the reference and alternative allele, and let the differential binding score be $D = \log(W/Z)$.

1. If $W$ and $Z$ are independent and uniform on $[0, 1]$ (the null hypothesis), then $D$ has the Laplace$(0, 1)$ distribution with density $\tfrac12 e^{-|x|}$.
2. Let $X_1, \dots, X_n$ be independent Laplace$(0, b)$ variables, $b > 0$, with density $\tfrac{1}{2b}e^{-|x|/b}$, and $Y = \max_i |X_i|$. Then $|X_i|$ is exponential with mean $b$, and

$$P(Y \le x) = \bigl(1 - e^{-x/b}\bigr)^n, \qquad f_Y(x) = \frac{n}{b}\,e^{-x/b}\bigl(1 - e^{-x/b}\bigr)^{n-1}, \qquad x \ge 0.$$

The maximal differential score $D_{\max}$ over the $n = 2m$ subsequences overlapping the variant on both strands is modelled by this law, with $b$ fitted per transcription-factor model (by the moment relation $\operatorname{Var} = 2b^2$, or by maximizing $\sum_j \log f_Y(x_j)$ over observed maxima $x_j$), and the $p$-value of an observed maximum $x$ is $1 - (1 - e^{-x/b})^n$.

## Depends on

- [Laplace distribution](../../../../Probability/distributions/continuous/laplace-distribution/laplace-measure.md)

## Expansion

$-\log W$ and $-\log Z$ are independent standard exponentials and $D = (-\log Z) - (-\log W)$; the difference of two independent $\mathrm{Exp}(1)$ variables is Laplace$(0, 1)$. Folding the Laplace density at zero gives the exponential law of $|X_i|$, and the CDF of a maximum of independent variables is the product of their CDFs. In practice the two $p$-values are positively dependent (the sequences differ in one base), so the empirical score is closer to Laplace with a scale $b \ne 1$, and the overlapping windows are not independent; the fitted $b$ absorbs part of this.

## Sources

- N. Baumgarten, L. Rumpf, T. Kessler and M. H. Schulz, "A statistical approach for identifying single nucleotide variants that affect transcription factor binding", iScience 27 (2024) 109765, <https://doi.org/10.1016/j.isci.2024.109765>, PMCID PMC11088338. STAR Methods: Equation 2, Theorem 1, Equations 3–8, Theorem 2 and Equation 9.
