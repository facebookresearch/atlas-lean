# Variance bound for the LD-score regression estimator

For a finite measure $\mu$, natural numbers $N$ and $M$, real numbers $\ell_1, \dots, \ell_M$ and
square-integrable statistics $\chi_1, \dots, \chi_M$ with
$\sum_k |\operatorname{Cov}(\chi_j, \chi_k)| \leq R$ for every $j$, the estimator
$\hat h^2 = \hat b\, M / N$, with $\hat b$ the least-squares slope $S_{\ell\chi} / S_{\ell\ell}$ of
the statistics on $\ell$, where $S_{xy} = \sum_j (x_j - \bar x)(y_j - \bar y)$, satisfies

$$\operatorname{Var}(\hat h^2) \leq \Bigl(\frac{M}{N}\Bigr)^2 \frac{R}{S_{\ell\ell}},$$

with variance and covariances taken with respect to $\mu$ and the convention $x/0 = 0$. For LD
scores $\ell_j$ this is the [unweighted estimator](ols-h2-hat.md).
