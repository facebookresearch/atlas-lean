# Covariance of the mean pairwise difference and the number of segregating sites

Let $\mu$ be a probability measure on a measurable space $(\Omega, \mathcal{F})$, let $(T_k)$ be Kingman holding times of a sample of size $n \ge 2$ under $\mu$, with total branch length $L$, let $\mathcal{G} \subseteq \mathcal{F}$ be a sub-σ-algebra and $\theta$ a real number. Suppose that

- $S$ is square-integrable and $\mathbb{E}[S \mid \mathcal{G}] = \frac{\theta}{2} L$ almost surely;
- for each [pair](sample-pairs.md) $s$ of genes of the sample: $\tau_s$ has the exponential distribution with rate $1$; $\mathbb{E}[\tau_s L] = 2 a_1(n) + (n+2)/n$; $D_s$ is square-integrable; $\mathbb{E}[D_s \mid \mathcal{G}] = \theta \tau_s$ almost surely; and $\mathbb{E}[D_s S \mid \mathcal{G}] = \frac{\theta^2}{2} \tau_s L + \theta \tau_s$ almost surely.

Then the [mean number of pairwise differences](mean-pair-diff.md) $\pi$ satisfies

$$\operatorname{Cov}(\pi, S) = \theta + \frac{n+2}{2n}\, \theta^2.$$

This is the covariance behind Tajima's constants $c_1$ and $c_2$.

## Sources

- F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA polymorphism*, Genetics 123 (1989), 585–595.
