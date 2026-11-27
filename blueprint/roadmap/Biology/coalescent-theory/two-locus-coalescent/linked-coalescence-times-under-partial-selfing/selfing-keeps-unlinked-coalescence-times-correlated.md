# Selfing keeps unlinked coalescence times correlated

In the diploid Wright–Fisher model with constant selfing probability $s_N = s \in (0,1)$ and recombination, sample both chromosomes of a single individual at two loci (configuration $q_{12}$). Then the large-$N$ [correlation of the two pairwise coalescence times](correlation-of-two-locus-coalescence-times-under-selfing-and-recombination.md) does not vanish for unlinked loci. At free recombination ($r_N = 1/2$, so $R = 1/2$),

$$\lim_{N\to\infty}\operatorname{Corr}_{q_{12}}[T_i,T_j] = \frac{s}{4-s} > 0,$$

and at the largest recombination rates

$$\lim_{N\to\infty}\operatorname{Corr}_{q_{12}}[T_i,T_j] \longrightarrow \frac{s}{2}$$

both as $\tilde\rho\to\infty$ when $r_N = \tilde\rho/N$, and as $r\to1$ when $r_N = r$ (where $R = (1-r)^2+r^2 \to 1$ in $\frac{(2-s)^2}{2(2-sR)}+s-1$). In contrast, without selfing ($s=0$) or with $s_N = O(1/N)$ the correlation is $O(1/N)$ once $r_N$ is of order one.

**Consequence for estimating $\theta$.** Let $\hat\theta_{(n)} = n^{-1}\sum_{k=1}^n\hat\theta_k$ be Tajima's estimator of $\theta = 4N\mu$ averaged over $n$ loci, each $\hat\theta_k$ the pairwise difference count at locus $k$ under the infinite-sites model with per-locus mutation rate $\mu$. For fixed $N$ and exchangeable loci,

$$\lim_{n\to\infty}\operatorname{Var}_q[\hat\theta_{(n)}] = 4\mu^2\operatorname{Cov}_q[T_i,T_j].$$

Since $\operatorname{Cov}_{q_{12}}[T_i,T_j]$ is of order $N^2$ under constant selfing (in scenario (iv), $\operatorname{Cov}_{q_{12}}\sim\bigl(\frac{2(1-s)(2-s)^2}{2-sR} - 4(1-s)^2\bigr)N^2$) and $\mu = \theta/(4N)$, the variance of Tajima's estimator stays bounded away from zero in the joint limit $n\to\infty$, $N\to\infty$, maximal recombination: adding unlinked loci cannot average away the genealogical noise shared through the individual's selfing history.

## Depends on

- [Correlation of two-locus coalescence times under partial selfing and recombination](correlation-of-two-locus-coalescence-times-under-selfing-and-recombination.md)

## Expansion

The limits are read off from the scenario (ii) and (iv) formulas: in scenario (ii) the $\tilde\rho^2$ terms dominate and give $4s(1-s)^2/(8(1-s)^2) = s/2$; in scenario (iv) setting $R=1$ gives $(2-s)/2 + s - 1 = s/2$ and $R = 1/2$ gives $s/(4-s)$. Intuitively, two copies of a locus in one individual coalesce during the run of selfing generations before the first outcrossing with probability $s/(2-s)$; the two loci share that individual's selfing history, so the instantaneous-coalescence events at the two loci are positively correlated however strongly the loci recombine. The variance identity is the law of total covariance: given the genealogies, mutation counts at distinct loci are independent Poisson variables with means proportional to $T_i, T_j$, so the $\operatorname{Var}[\hat\theta_k]/n$ term disappears and only the inter-locus covariance remains.

## Sources

- David Kogan, Dimitrios Diamantidis, John Wakeley and Wai-Tong Louis Fan, "Correlation of coalescence times in a diploid Wright–Fisher model with recombination and selfing", *Theoretical Population Biology* 167 (2026), 40–68, <https://doi.org/10.1016/j.tpb.2025.11.003>. Numbering as in the preprint arXiv:2310.12435v1, <https://arxiv.org/abs/2310.12435v1>: Theorem 1 (iv), Corollary 1 (ii), (iv), and Section 4, subsection "Variance of Tajima's estimator".
