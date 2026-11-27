# Heterochronous Λ-coalescent likelihood with variable effective population size

Let $\Lambda$ be a finite measure on $[0,1]$ and, for $2 \le k \le b$, let

$$\lambda_{b,k} = \int_0^1 x^{k-2}(1-x)^{b-k}\,\Lambda(dx)$$

be the rate at which a given $k$-block merges when $b$ lineages are present. Consider a rooted, timed multifurcating genealogy of $n$ haploid samples collected at $L$ sampling times $s_1 = 0 < s_2 < \dots < s_L$ (with $n_\ell$ samples at $s_\ell$, $\sum_\ell n_\ell = n$), with no simultaneous mergers. Let $t_1 < \dots < t_K$ be the coalescent times, $m_k \ge 2$ the number of lineages merging at $t_k$, and $A(t)$ the number of lineages extant at time $t$ (backwards). If the merger rates are scaled by a positive effective population size trajectory $N_e(t)$, the density of the block sizes $m = (m_k)$ and times $t = (t_k)$ is

$$p(m, t \mid n, s, N_e, \Lambda) = \exp\!\left(-\int_0^\infty \sum_{j=2}^{A(u)} \frac{\binom{A(u)}{j}\lambda_{A(u),j}}{N_e(u)}\,du\right) \prod_{k=1}^{K} \frac{\binom{A(t_k)}{m_k}\lambda_{A(t_k),m_k}}{N_e(t_k)}.$$

It factors into the density of a point process of coalescent events with total rate $\lambda_{A(t)}/N_e(t)$, where $\lambda_b = \sum_{j=2}^{b}\binom{b}{j}\lambda_{b,j}$, and the conditional probability of the observed block sizes,

$$P(m \mid n, \Lambda) = \prod_{k=1}^{K} \frac{\binom{A(t_k)}{m_k}\lambda_{A(t_k),m_k}}{\lambda_{A(t_k)}},$$

which does not involve $N_e$. For the Beta$(2-\alpha,\alpha)$-coalescent, $\lambda_{b,k} = B(k-\alpha, \alpha+b-k)/B(2-\alpha,\alpha)$, so the block sizes alone give a pseudo-likelihood estimator $\hat\alpha^{BS} = \arg\max_\alpha P(m \mid n, \alpha)$, while coalescent times and block sizes together are the sufficient statistics for $(N_e, \alpha)$.

## Depends on

- [Closed form of the Beta-coalescent rates](../merger-rates-and-beta-coalescents/merger-rate-beta-lambda.md)
- [Skyline estimate of population size](../../skyline-plot-estimates-of-population-size/skyline-estimate.md)
- [Pitman's merger rate](../../coalescents/merger-rate.md)
- [Total merger rate of a Λ-coalescent](../../coalescents/total-merger-rate.md)

## Expansion

Between consecutive event times the number of lineages is constant, so each waiting time is exponential with rate $\lambda_{A(t)}/N_e(t)$, and heterochronous sampling only changes $A(t)$ at the sampling times. Given that an event occurs with $b$ lineages, the merging block has size $k$ with probability $\binom{b}{k}\lambda_{b,k}/\lambda_b$, and its members are chosen uniformly. Multiplying the survival factor by the event densities gives the formula; dividing out the total rate isolates the block-size factor. With $\Lambda = \delta_0$ only binary mergers occur and the density reduces to the variable-size Kingman coalescent likelihood. In practice $\log N_e(t)$ is given a piecewise-constant Gaussian Markov random field prior and the integral is replaced by a Riemann sum.

## Sources

- J. Zhang and J. A. Palacios, "Multiple merger coalescent inference of effective population size", *Philosophical Transactions of the Royal Society B* (2025), Section 2, Eqs. (2.1)–(2.4), and Section 3, Eq. (3.1). <https://doi.org/10.1098/rstb.2023.0306> (PMC11867189)
