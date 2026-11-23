# Tajima's variance identity

Let $\mu$ be a probability measure, let $(T_k)$ be Kingman holding times of a sample of size $n \ge 2$ under $\mu$, with total branch length $L$, let $\mathcal{G}$ be a sub-σ-algebra and $\theta$ a real number. Assume the hypotheses of [Variance of the mean number of pairwise differences](variance-mean-pair-diff.md) on $\tau_s$, $\ell_{st}$ and $D_s$, and in addition that

- $S$ is square-integrable, with conditional mean and conditional variance given $\mathcal{G}$ both equal to $\frac{\theta}{2} L$ almost surely;
- for each pair $s$, $\mathbb{E}[\tau_s L] = 2 a_1(n) + (n+2)/n$ and $\mathbb{E}[D_s S \mid \mathcal{G}] = \frac{\theta^2}{2} \tau_s L + \theta \tau_s$ almost surely.

Then, with the [mean number of pairwise differences](mean-pair-diff.md) $\pi$ and [Tajima's constants](tajima-c1.md),

$$\operatorname{Var}\Bigl(\pi - \frac{S}{a_1(n)}\Bigr) = c_1(n)\, \theta + c_2(n)\, \theta^2.$$

## Sources

- F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA polymorphism*, Genetics 123 (1989), 585–595.
