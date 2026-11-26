# Expected frequency spectrum and discovery curve of a variant-frequency histogram

Let a class of variant sites have population frequencies described by a **frequency histogram** $h$: a finite set $X \subset (0,1]$ and numbers $h(x) \ge 0$, where $h(x)$ is the number of sites whose non-reference allele has population frequency $x$. Sample $k$ alleles independently, so that a site of frequency $x$ is seen in $i$ of them with probability $\mathrm{bin}(x,k,i) = \binom{k}{i} x^i (1-x)^{k-i}$, independently across sites. Let $F_i$ be the number of sites observed in exactly $i$ of the $k$ alleles, $1 \le i \le k$ (the sample site frequency spectrum). Then:

1. **Expected spectrum.** $\mathbb E[F_i] = \sum_{x \in X} h(x)\,\mathrm{bin}(x,k,i)$.
2. **Discovery curve.** The expected number of distinct variants observed in a sample of $N$ alleles is

$$D(N) = \sum_{x \in X} h(x)\left(1 - (1-x)^N\right).$$

$D$ is nondecreasing and concave in $N$, with increments $D(N+1) - D(N) = \sum_x h(x)\,x(1-x)^N = \mathbb E[F_1^{(N+1)}]/(N+1)$, where $F_1^{(N+1)}$ is the number of singletons in a sample of $N+1$ alleles, and $D(N) \to \sum_x h(x)$ as $N \to \infty$.
3. **Limit of identifiability.** Each $\mathbb E[F_i]$, $i \le k$, depends on $h$ only through the moments $m_j = \sum_x h(x) x^j$ for $1 \le j \le k$, whereas $D(N) = \sum_{j=1}^N (-1)^{j+1}\binom{N}{j} m_j$ involves moments up to order $N$. Two histograms with the same first $k$ moments produce the same expected spectrum in a cohort of $k$ alleles but can have different discovery curves for $N > k$; extrapolation beyond the sampled size is therefore a regularised inverse problem rather than a direct computation.

## Depends on

- [Binomial probability mass function](../../../cancer-genomics/detection-power-for-somatic-mutations/binom-pmf.md): $\mathrm{bin}(x,k,i)$

## Proof depends on

- [The Good–Turing identity for the missing mass](../../../not-yet-classified/good-turing/expect-missing-mass.md): the increment of the discovery curve

## Expansion

Item 1 is linearity of expectation over sites. For item 2, a site of frequency $x$ is missed by all $N$ alleles with probability $(1-x)^N$. The increment formula follows from $(1-x)^N - (1-x)^{N+1} = x(1-x)^N$, which is decreasing in $N$ (concavity), and from $\mathbb E[F_1^{(N+1)}] = (N+1)\sum_x h(x) x (1-x)^N$; this is the Good–Turing identity that the expected number of new variants found by one more allele equals the expected singleton count divided by the sample size. Item 3 follows by expanding $\mathrm{bin}(x,k,i)$ and $(1-x)^N$ binomially. Zou et al. use the expected spectrum as the forward model of their estimator, and the discovery curve to predict how many protein-coding variants, and how many genes carrying loss-of-function variants, cohorts larger than the 60,706 exomes of ExAC would observe.

## Sources

- J. Zou, G. Valiant, P. Valiant, K. Karczewski, S. O. Chan, K. Samocha, M. Lek, S. Sunyaev, M. Daly, D. G. MacArthur, "Quantifying unobserved protein-coding variants in human populations provides a roadmap for large-scale sequencing projects", Nature Communications 7 (2016), 13293, <https://doi.org/10.1038/ncomms13293> (PMC5095512), Methods, "UnseenEst algorithm".
