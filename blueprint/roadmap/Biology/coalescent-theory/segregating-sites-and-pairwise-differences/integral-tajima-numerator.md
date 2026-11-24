# Tajima's numerator has mean zero

Let $\mu$ be a measure on a measurable space $(\Omega, \mathcal{F})$, let $(T_k)$ be Kingman holding times of a sample of size $n \ge 2$ under $\mu$, with total branch length $L$, and let $\mathcal{G} \subseteq \mathcal{F}$ be a sub-σ-algebra on which $\mu$ is σ-finite. Let $\theta$ be a real number and suppose that

- $S$ is a $\mu$-integrable real function whose conditional expectation given $\mathcal{G}$ equals $\frac{\theta}{2} L$ $\mu$-almost everywhere;
- for each [pair](sample-pairs.md) $s$ of genes of the sample, $\tau_s$ has the exponential distribution with rate $1$ under $\mu$, $D_s$ is $\mu$-integrable, and the conditional expectation of $D_s$ given $\mathcal{G}$ equals $\theta \tau_s$ $\mu$-almost everywhere.

Then, with the [mean number of pairwise differences](mean-pair-diff.md) $\pi$ and [Tajima's constant](tajima-a1.md) $a_1(n)$,

$$\int \Bigl(\pi - \frac{S}{a_1(n)}\Bigr) d\mu = 0.$$

## Sources

- F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA polymorphism*, Genetics 123 (1989), 585–595.
