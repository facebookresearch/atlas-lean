# Expected pairwise differences

Let $\mu$ be a measure on a measurable space $(\Omega, \mathcal{F})$, let $\mathcal{G} \subseteq \mathcal{F}$ be a sub-σ-algebra on which $\mu$ is σ-finite, let $n \ge 2$ and let $\theta$ be a real number. For each [pair](sample-pairs.md) $s$ of genes of a sample of size $n$, let $\tau_s$ and $D_s$ be real functions on $\Omega$ such that

- $\tau_s$ has the exponential distribution with rate $1$ under $\mu$,
- $D_s$ is $\mu$-integrable, and
- the conditional expectation of $D_s$ given $\mathcal{G}$ equals $\theta \tau_s$ $\mu$-almost everywhere.

Then the [mean number of pairwise differences](mean-pair-diff.md) $\pi = \binom{n}{2}^{-1} \sum_s D_s$ satisfies $\int \pi \, d\mu = \theta$. Here $\tau_s$ is the coalescence time of the pair, $D_s$ its number of differences, and mutations fall at rate $\theta/2$ on each of the two branches of length $\tau_s$; since $n \ge 2$, the first condition forces $\mu$ to be a probability measure.

## Sources

- F. Tajima, *Evolutionary relationship of DNA sequences in finite populations*, Genetics 105 (1983), 437–460.
