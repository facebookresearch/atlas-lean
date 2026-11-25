# Variance of the mean number of pairwise differences

Let $\mu$ be a probability measure on a measurable space $(\Omega, \mathcal{F})$, let $\mathcal{G} \subseteq \mathcal{F}$ be a sub-σ-algebra, $n \ge 2$ and $\theta$ a real number. For [pairs](sample-pairs.md) $s$, $t$ of genes of a sample of size $n$, let $\tau_s$, $D_s$ and $\ell_{st}$ be real random variables such that

- each $\tau_s$ has the exponential distribution with rate $1$;
- $\mathbb{E}[\tau_s \tau_t] = 4/3$ when $s$ and $t$ share exactly one gene, and $\mathbb{E}[\tau_s \tau_t] = 11/9$ when they are disjoint;
- $\ell_{ss} = 2 \tau_s$ almost surely; $\ell_{st} = \tau_s + \tau_t - \tau_{s \triangle t}$ almost surely when $s$ and $t$ share exactly one gene ($s \triangle t$ is their symmetric difference); and $\mathbb{E}[\ell_{st}] = 2/3$ when they are disjoint;
- each $D_s$ is square-integrable, $\mathbb{E}[D_s \mid \mathcal{G}] = \theta \tau_s$ almost surely, and $\mathbb{E}[D_s D_t \mid \mathcal{G}] = \theta^2 \tau_s \tau_t + \frac{\theta}{2} \ell_{st}$ almost surely.

Then the [mean number of pairwise differences](mean-pair-diff.md) $\pi$ satisfies

$$\operatorname{Var}(\pi) = b_1(n)\, \theta + b_2(n)\, \theta^2,$$

with [Tajima's constants](tajima-b1.md) $b_1$ and $b_2$. Here $\ell_{st}$ is the length of the part of the genealogy shared by the paths of the two pairs.

## Sources

- F. Tajima, *Evolutionary relationship of DNA sequences in finite populations*, Genetics 105 (1983), 437–460.
