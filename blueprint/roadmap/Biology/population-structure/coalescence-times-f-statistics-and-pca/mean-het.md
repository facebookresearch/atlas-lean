# Mean heterozygosity between populations

Let $\mu$ be a measure on a measurable space $\Omega$ and $p_X : \Omega \to \mathbb{R}$ the allele frequency of each population $X$. The mean heterozygosity between populations $X$ and $Y$ is

$$\pi(X, Y) = \int h(p_X, p_Y) \, d\mu,$$

where $h$ is the [pairwise difference probability](het-pair.md), with the convention that the integral of a non-integrable function is $0$. When $\mu$ is a probability measure and the frequencies lie in $[0, 1]$, it is the expected heterozygosity between $X$ and $Y$, and for $Y = X$ the expected heterozygosity within $X$.
