# Posterior probability that the cancer cell fraction exceeds a threshold

For $m$ grid points $c_1, \dots, c_m$ with prior weights $\pi_1, \dots, \pi_m$, purity $\alpha$, copy number $q$, natural numbers $n$ (reads) and $a$ (variant reads), and a threshold $t$, the posterior tail is

$$P(c > t \mid a) = \frac{\sum_{k \,:\, c_k > t} \pi_k B(a \mid n, f(c_k))}{\sum_k \pi_k B(a \mid n, f(c_k))}, \qquad f(c) = \frac{\alpha c}{\alpha q + 2(1 - \alpha)},$$

where $B(a \mid n, p) = \binom{n}{a} p^a (1 - p)^{n - a}$, with the convention $x/0 = 0$ (Landau et al. 2013). It is a posterior probability when every weight $\pi_k B(a \mid n, f(c_k))$ is nonnegative and their sum is positive, as in a [grid model](grid-model.md) with $a \le n$.

## Sources

- D. A. Landau et al., *Evolution and impact of subclonal mutations in chronic lymphocytic leukemia*, Cell 152 (2013), 714–726.
