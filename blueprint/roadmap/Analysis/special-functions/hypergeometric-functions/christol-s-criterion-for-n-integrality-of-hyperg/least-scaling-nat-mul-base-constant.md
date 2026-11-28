# Least rescaling making a hypergeometric series integral

Least rescaling, general form (Delaygue–Rivoal–Roques, Theorem 4, first part). Let $\alpha$ and $\beta$
be finite multisets of admissible rational parameters (no parameter in $\mathbb{Z}_{\le 0}$), and suppose
the series with coefficients $\prod_i (\alpha_i)_n / \prod_j (\beta_j)_n$ is $N$-integral, that is,
$C^n \prod_i (\alpha_i)_n / \prod_j (\beta_j)_n \in \mathbb{Z}$ for all $n \ge 0$ for some rational
$C > 0$ (call such a $C$ a good scaling). Then there is a positive integer $K$ such that
$K \cdot \mathrm{baseConstant}(\alpha, \beta)$ is a good scaling and is at most every positive good
scaling, so it is the least one. Here
$\mathrm{baseConstant}(\alpha, \beta) = \frac{\prod_i \mathrm{den}(\alpha_i)}{\prod_j \mathrm{den}(\beta_j)} \prod_p p^{-\lfloor \lambda_p / (p - 1) \rfloor}$,
with $\lambda_p = \#\{i : p \nmid \mathrm{den}(\alpha_i)\} - \#\{j : p \nmid \mathrm{den}(\beta_j)\}$ and
$p$ running over the primes that divide the least common multiple of the denominators of the parameters
or satisfy $p \le |\alpha| - |\beta| + 1$. In general $K$ is not specified further; see
[Exact least rescaling for N-integral series with parameters in (0, 1\]](least-scaling-eq-base-constant.md)
for the case $K = 1$.

Both admissibility and $N$-integrality are needed. If $N$-integrality is dropped there may be no good
scaling at all: for $\alpha = (1)$ and $\beta = (1/2)$ the coefficients are $4^n / \binom{2n}{n}$, and for
any positive rational $C$ an odd prime $p$ dividing neither the numerator nor the denominator of $C$
survives in the denominator of $C^n 4^n / \binom{2n}{n}$ at $n = (p + 1)/2$. If admissibility is dropped there
may be no least good scaling: an upper parameter $0$ makes the coefficients $1, 0, 0, \dots$, for which
every positive rational is a good scaling.

## Sources

- E. Delaygue, T. Rivoal, J. Roques, *On Dwork's $p$-adic formal congruences theorem and hypergeometric mirror maps*, Mem. Amer. Math. Soc. **246** (2017), no. 1163, §2.1, Theorem 4 (which assumes $N$-integrality throughout).
