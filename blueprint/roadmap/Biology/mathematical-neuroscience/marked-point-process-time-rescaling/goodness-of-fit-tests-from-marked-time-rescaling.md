# Goodness-of-fit tests from marked time-rescaling

Under a correctly specified joint mark intensity $\lambda(t,m\mid H_t)$, the [time-rescaling theorem for marked point processes](time-rescaling-theorem-for-marked-point-processes.md) makes the rescaled points $(\tau_j, m_j)$ i.i.d. uniform on the region $R = \{(\tau,m) : 0 \le \tau \le b(m)\}$ given their number $n$. Model checking therefore reduces to testing uniformity on $R$.

**Pearson test.** Partition $R$ into subregions $R_1,\dots,R_K$ with volumes $|R_i|$, let $r_i$ be the number of rescaled points in $R_i$ and $p_i = |R_i|/|R|$. With $np_i$ large (say above $5$),

$$X^2 = \sum_{i=1}^K \frac{(r_i - np_i)^2}{np_i}$$

is approximately $\chi^2_{K-1}$ under the model, and the model is rejected at level $\alpha$ when $X^2$ exceeds the $1-\alpha$ quantile of $\chi^2_{K-1}$.

**Kolmogorov–Smirnov tests.** Ignoring marks, the rescaled times form a Poisson process with intensity $\tilde\lambda(\tau) = \int\mathbf 1\{(\tau,m)\in R\}\,dm$; rescaling them once more by the univariate time-rescaling theorem gives unit-exponential intervals, which are compared with the exponential distribution in a KS plot. Restricting to any subregion $R_s \subset R$ (a range of marks) gives a Poisson process with intensity $\int\mathbf 1\{(\tau,m)\in R_s\}\,dm$, so misfit localized to particular marks (e.g. one neuron) can be detected even when the pooled test passes. Alternatively, normalized rescaled times $\tilde\tau_j = \tau_j(m_j)/b(m_j) \in [0,1]$ can be pooled across marks and their intervals compared directly against an exponential law with rate $N(T)$.

## Depends on

- [Time-rescaling theorem for marked point processes](time-rescaling-theorem-for-marked-point-processes.md)

## Expansion

The chi-square statistic is the standard multinomial goodness-of-fit statistic: conditionally on $n$, uniform points fall into the $R_i$ with probabilities $p_i$. The KS route uses the fact that thinning or restricting a Poisson process to a subregion again gives a Poisson process whose intensity is the measure of the corresponding mark-section of $R$. The two families are complementary: the chi-square test is sensitive to spatial misallocation of points across the time–mark region, the KS tests to temporal structure.

## Sources

- L. Tao, K. E. Weber, K. Arai, U. T. Eden, "A common goodness-of-fit framework for neural population models using marked point process time-rescaling", Journal of Computational Neuroscience (2018), Section 2 (assessing goodness-of-fit, Eq. (13) and Corollary 2) and Sections 3–4, <https://doi.org/10.1007/s10827-018-0698-4>, PMCID PMC6208891.
