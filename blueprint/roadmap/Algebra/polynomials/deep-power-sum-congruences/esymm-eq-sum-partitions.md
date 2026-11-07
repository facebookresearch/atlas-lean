# Elementary symmetric polynomials in terms of power sums

Let $\sigma$ be a finite set of
variables, and in $\mathbb{Q}[x_i : i \in \sigma]$ let $e_n$ be the $n$-th elementary symmetric
polynomial and $p_k = \sum_{i \in \sigma} x_i^k$ the $k$-th power sum. For a partition $\lambda$
of $n$ with parts $\lambda_1, \dots, \lambda_\ell$, write
$p_\lambda = p_{\lambda_1} \cdots p_{\lambda_\ell}$, $\varepsilon_\lambda = (-1)^{n - \ell}$ and
$z_\lambda = \prod_a a^{r_a} \, r_a!$, where $r_a$ is the number of parts equal to $a$ and the
product runs over the distinct parts $a$. Then for every $n \ge 0$,

$$e_n = \sum_{\lambda \vdash n} \frac{\varepsilon_\lambda}{z_\lambda} \, p_\lambda.$$

## Sources

- S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, Corollary 21 (`integers-2024-A46-cor-21`).
