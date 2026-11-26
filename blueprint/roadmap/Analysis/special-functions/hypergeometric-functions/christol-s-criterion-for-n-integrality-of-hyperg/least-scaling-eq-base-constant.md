# Exact least rescaling for N-integral series with parameters in (0, 1]

Least rescaling, exact form (Delaygue–Rivoal–Roques, Theorem 4, second part). Let $\alpha$ and $\beta$
be finite multisets of rational parameters with the same cardinality and every parameter in $(0, 1]$
(so all are admissible), and suppose the series with coefficients $\prod_i (\alpha_i)_n / \prod_j (\beta_j)_n$
is $N$-integral, that is, some rational $C > 0$ makes every $C^n \prod_i (\alpha_i)_n / \prod_j (\beta_j)_n$
an integer (a good scaling). Then $\mathrm{baseConstant}(\alpha, \beta)$, defined on
[Least rescaling making a hypergeometric series integral](least-scaling-nat-mul-base-constant.md), is
itself a good scaling and is at most every positive good scaling, so it is the least one. For example,
with $\alpha = \{1/2, 1/2\}$ and $\beta = \{1, 1\}$ the base constant is $16$, and the rescaled coefficients
are the squared central binomial coefficients.

$N$-integrality is a genuine hypothesis here: $\alpha = (1)$ and $\beta = (1/2)$ have the same length and
lie in $(0, 1]$, yet the coefficients $4^n / \binom{2n}{n}$ admit no positive rational good scaling (for any
$C$, an odd prime $p$ dividing neither the numerator nor the denominator of $C$ survives in the
denominator at $n = (p + 1)/2$).

## Sources

- E. Delaygue, T. Rivoal, J. Roques, *On Dwork's $p$-adic formal congruences theorem and hypergeometric mirror maps*, Mem. Amer. Math. Soc. **246** (2017), no. 1163, §2.1, Theorem 4 (which assumes $N$-integrality throughout).
