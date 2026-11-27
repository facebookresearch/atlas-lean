# Unbiased estimator of Tajima's variance term

Let $\mu$ be a probability measure on a measurable space $(\Omega, \mathcal{F})$, let $(T_k)$ be Kingman holding times of a sample of size $n \ge 2$ under $\mu$, with total branch length $L$, and let $\mathcal{G} \subseteq \mathcal{F}$ be a sub-σ-algebra. Let $\theta$ be a real number and $S$ a square-integrable real random variable whose conditional mean and conditional variance given $\mathcal{G}$ both equal $\frac{\theta}{2} L$ almost surely. Then

$$\mathbb{E}\bigl[e_1(n)\, S + e_2(n)\, S(S-1)\bigr] = c_1(n)\, \theta + c_2(n)\, \theta^2,$$

where $c_1, c_2, e_1, e_2$ are [Tajima's constants](tajima-e1.md). By [Tajima's variance identity](variance-tajima-numerator.md), $c_1 \theta + c_2 \theta^2$ is the variance of $\pi - S/a_1$ under the hypotheses stated there.

## Sources

- F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA polymorphism*, Genetics 123 (1989), 585–595.
