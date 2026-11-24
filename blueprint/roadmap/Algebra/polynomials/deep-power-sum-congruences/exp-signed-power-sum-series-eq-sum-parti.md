# Exponential of a power-sum series restricted to a set of degrees

Let $\sigma$ be a finite
set of variables, and in $\mathbb{Q}[x_i : i \in \sigma]$ let $p_s = \sum_{i \in \sigma} x_i^s$
be the $s$-th power sum. Let $S$ be a set of natural numbers and let
$P_S(t) = \sum_{s \in S,\ s \ge 1} \frac{(-1)^{s-1}}{s} p_s t^s$. For a partition $\lambda$ of
$n$ with parts $\lambda_1, \dots, \lambda_\ell$, write
$p_\lambda = p_{\lambda_1} \cdots p_{\lambda_\ell}$, $\varepsilon_\lambda = (-1)^{n - \ell}$ and
$z_\lambda = \prod_a a^{r_a} \, r_a!$, where $r_a$ is the number of parts equal to $a$ and the
product runs over the distinct parts $a$. Then, as formal power series in $t$ with coefficients
in $\mathbb{Q}[x_i : i \in \sigma]$, $\exp P_S(t) = \sum_{n \ge 0} c_n t^n$, where $c_n$ is the
sum of $\varepsilon_\lambda p_\lambda / z_\lambda$ over the partitions $\lambda$ of $n$ all of
whose parts lie in $S$.

## Sources

- S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, Proposition 19.
