# Log-odds affinity under the extended hypergeometric model

**Urn model.** On $N$ sites, species $A$ occupies a uniformly random set of $m_A$ sites. Species $B$ then occupies each site independently, with probability $p_1$ if $A$ is present and $p_2$ if not. Let $X$ be the number of sites occupied by both species.

**Theorem (affinity parameter).** Conditional on $B$ occupying exactly $m_B$ sites, the law of $X$ depends on $(p_1,p_2)$ only through the log odds ratio

$$\alpha=\log\frac{p_1(1-p_2)}{p_2(1-p_1)},$$

and is the extended hypergeometric distribution

$$\Pr(X=k)=\frac{\binom{m_A}{k}\binom{N-m_A}{m_B-k}e^{k\alpha}}{\sum_{j=L}^{U}\binom{m_A}{j}\binom{N-m_A}{m_B-j}e^{j\alpha}},\qquad L=\max(m_A+m_B-N,0)\le k\le U=\min(m_A,m_B).$$

The distribution is unchanged if the roles of $A$ and $B$ are swapped; $\alpha=0$ gives the hypergeometric null of random assortment, and in the log-linear model $\log\mu_{ij}=\lambda+\lambda^A_i+\lambda^B_j+\lambda^{AB}_{ij}$ of the $2\times2$ table the log odds ratio is $\alpha=\lambda^{AB}_{11}+\lambda^{AB}_{22}-\lambda^{AB}_{12}-\lambda^{AB}_{21}$, so with sum-to-zero constraints the row–column interaction is $\lambda^{AB}_{11}=\alpha/4$, and with indicator coding ($\lambda^{AB}_{ij}=0$ unless $i=j=1$) it equals $\alpha$ (Agresti). The source prints that $\alpha$ "is ¼ times the row-column interaction parameter"; the page states the reverse relation $\alpha=4\lambda^{AB}_{11}$, which is what the displayed identity gives under sum-to-zero constraints.

**Estimation and intervals.**

- The maximum likelihood estimate $\hat\alpha$ maximises the probability above at the observed $X$; it is approximately normal when $\min(m_A,m_B,N-m_A,N-m_B)$ is large. At the extreme counts $X=L$ or $X=U$ the maximiser is $\mp\infty$, and a capped value $\mp\log(2N^2)$ is reported.
- The distribution function $F(x,\alpha)=\Pr(X\le x)$ is strictly decreasing in $\alpha$ for $L<x<U$, tending to $1$ as $\alpha\to-\infty$ and to $0$ as $\alpha\to\infty$. Since $x$ is a median of $X$ iff $F(x,\alpha)\ge1/2$ and $F(x-1,\alpha)\le1/2$, the set of $\alpha$ for which $x$ is a median of $X$ is the closed interval $\big[F(x-1,\cdot)^{-1}(1/2),\,F(x,\cdot)^{-1}(1/2)\big]$; its interior, the largest open interval of such $\alpha$, is the *median interval* $\big(F(x-1,\cdot)^{-1}(1/2),\,F(x,\cdot)^{-1}(1/2)\big)$ of the source, whose length measures the discreteness of the data.
- Because the family has a monotone likelihood ratio in $x$, the equal-tailed level-$\gamma$ test of $\alpha=\alpha_0$ rejects for $X\le k_1$ or $X\ge k_2$; inverting it gives the exact (Clopper–Pearson-type) interval $\{\alpha:\ \Pr_\alpha(X\le x)>\gamma/2,\ \Pr_\alpha(X\ge x)>\gamma/2\}$, whose true coverage is at least the nominal level.

## Expansion

Conditioning on the occupied sites of $A$, the number of $A$-sites also holding $B$ is $\mathrm{Bin}(m_A,p_1)$ and the number of non-$A$ sites holding $B$ is $\mathrm{Bin}(N-m_A,p_2)$; conditioning on their sum $m_B$ gives weights $\binom{m_A}{k}\binom{N-m_A}{m_B-k}p_1^k(1-p_1)^{m_A-k}p_2^{m_B-k}(1-p_2)^{N-m_A-m_B+k}$, and dividing by the $k$-free factors leaves $e^{k\alpha}$. This is a one-parameter exponential family in $\alpha$ with sufficient statistic $X$, which gives monotonicity of $F$ in $\alpha$, the monotone likelihood ratio, and Karlin–Rubin optimal one-sided tests. Traditional co-occurrence indices (Jaccard, Sørensen and similar) depend on prevalences and can rank the same association differently across datasets; $\alpha$ separates association from prevalence.

## Sources

- Mainali KP, Slud E, "CooccurrenceAffinity: An R package for computing a novel metric of affinity in co-occurrence data that corrects for pervasive errors in traditional indices" (2025), Section "Models, parameters and intervals" (urn model, equations (1)-(3), the maximum likelihood estimator and its capping, the median interval and the test-inverted confidence intervals), <https://doi.org/10.1371/journal.pone.0316650>, PMCID PMC11737770.
- A. Agresti, *Categorical Data Analysis*, 2nd ed., Wiley (2002), Section 8.1 (log-linear models for two-way tables; the odds ratio in terms of the association parameters under sum-to-zero and baseline-category constraints).
