# Maximum-likelihood cancer cell fraction

For purity $\alpha$, copy number $q$ and natural numbers $n, a$, put

$$\hat c = \min\Bigl(1, \frac{a / n}{\kappa}\Bigr), \qquad \kappa = \frac{\alpha}{\alpha q + 2(1 - \alpha)},$$

with the convention $x/0 = 0$. For $0 < \alpha \le 1$, $q \ge 1$, $n > 0$ and $a \le n$, $\hat c$ maximizes the binomial likelihood $c \mapsto \binom{n}{a} f(c)^a (1 - f(c))^{n - a}$, $f(c) = \alpha c/(\alpha q + 2(1 - \alpha))$, over $c \in [0, 1]$ ([the continuous CCF MLE](is-max-on-ccf-mle.md)); outside this domain $\hat c$ need not be a maximizer. Landau et al. (2013) use the grid posterior instead.

## Sources

- D. A. Landau et al., *Evolution and impact of subclonal mutations in chronic lymphocytic leukemia*, Cell 152 (2013), 714–726.
