# Goodness-of-fit tests from marked time-rescaling

Let the joint mark intensity $\lambda(t,m)$ be correctly specified and not depend on the process's own past. Then the [time-rescaling theorem for marked point processes](time-rescaling-theorem-for-marked-point-processes.md) makes the rescaled points $(\tau_j, m_j)$ i.i.d. uniform on the fixed region $R = \{(\tau,m) : 0 \le \tau \le b(m)\}$ given their number $n$, and model checking reduces to testing uniformity on $R$. For history-dependent intensities the tests below are approximate.

**Theorem.** Under these hypotheses:

1. given $n$, $|R| > 0$ and a fixed partition of $R$ into subregions $R_1,\dots,R_K$ of positive volume, with $p_i = |R_i|/|R|$, the counts $(r_1,\dots,r_K)$ of rescaled points in the $R_i$ are $\mathrm{Multinomial}(n; p_1,\dots,p_K)$, so $X^2 = \sum_{i=1}^K (r_i - np_i)^2/(np_i)$ converges in distribution to $\chi^2_{K-1}$ as $n \to \infty$;
2. for every measurable $R_s \subseteq R$, the rescaled times of the points in $R_s$ form a Poisson process with intensity $\int\mathbf 1\{(\tau,m)\in R_s\}\,dm$ (for $R_s = R$, the rescaled times ignoring marks);
3. given $n$, the normalized times $\tilde\tau_j = \tau_j(m_j)/b(m_j)$ are i.i.d. uniform on $[0,1]$.

**Pearson test.** With $np_i$ large (say above $5$), $X^2$ is approximately $\chi^2_{K-1}$ under the model, and the model is rejected at level $\alpha$ when $X^2$ exceeds the $1-\alpha$ quantile of $\chi^2_{K-1}$.

**Kolmogorov–Smirnov tests.** Ignoring marks, the rescaled times form a Poisson process with intensity $\tilde\lambda(\tau) = \int\mathbf 1\{(\tau,m)\in R\}\,dm$; rescaling them once more by the univariate time-rescaling theorem gives unit-exponential intervals, which are compared with the exponential distribution in a KS plot. Restricting to any subregion $R_s \subset R$ (a range of marks) gives a Poisson process with intensity $\int\mathbf 1\{(\tau,m)\in R_s\}\,dm$, so misfit localized to particular marks (e.g. one neuron) can be detected even when the pooled test passes. Alternatively, the normalized rescaled times $\tilde\tau_j$ can be pooled across marks and their intervals compared directly against an exponential law with rate $N(T)$.

## Depends on

- [Time-rescaling theorem for marked point processes](time-rescaling-theorem-for-marked-point-processes.md)

## Expansion

The chi-square statistic is the standard multinomial goodness-of-fit statistic: conditionally on $n$, uniform points fall into the $R_i$ with probabilities $p_i$. The KS route uses the fact that thinning or restricting a Poisson process to a subregion again gives a Poisson process whose intensity is the measure of the corresponding mark-section of $R$. The two families are complementary: the chi-square test is sensitive to spatial misallocation of points across the time–mark region, the KS tests to temporal structure.

## Sources

- L. Tao, K. E. Weber, K. Arai, U. T. Eden, "A common goodness-of-fit framework for neural population models using marked point process time-rescaling", Journal of Computational Neuroscience (2018), Section 2 (assessing goodness-of-fit, Eq. (13) and Corollary 2) and Sections 3–4, <https://doi.org/10.1007/s10827-018-0698-4>, PMCID PMC6208891.
