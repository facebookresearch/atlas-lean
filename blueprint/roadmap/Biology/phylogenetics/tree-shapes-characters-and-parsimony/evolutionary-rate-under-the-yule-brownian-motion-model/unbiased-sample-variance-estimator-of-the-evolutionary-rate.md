# Unbiased sample-variance estimator of the evolutionary rate

**Model.** A Yule (pure-birth) tree with birth rate $\lambda$ is conditioned to have $n$ tips at the observation time; along its branches a trait evolves as Brownian motion with variance $\sigma^2$ per unit time from $X_0$, independently after each split. The tip values $X^{(n)}_1,\dots,X^{(n)}_n$ have sample mean $\bar X_n$ and sample variance $S_n^2=\frac1{n-1}\sum_i(X^{(n)}_i-\bar X_n)^2$. The *evolutionary rate* is $\rho^2=\sigma^2/\lambda$. Let $H_n=\sum_{k=1}^n1/k$.

**Statements.**

1. *(Unbiasedness.)* $\mathbb{E}S_n^2=\big(\tfrac{n+1}{n-1}H_n-\tfrac{2n}{n-1}\big)\rho^2$, so

    $$R_n^2=\Big(\frac{n+1}{n-1}H_n-\frac{2n}{n-1}\Big)^{-1}S_n^2$$

    is an unbiased estimator of $\rho^2$.

2. *(Variance of the sample variance.)* As $n\to\infty$,

    $$\mathrm{Var}(S_n^2/\rho^2)=1+\frac{\pi^2}{6}+O(n^{-1}\log^2n).$$

3. *(Consistency and standard error.)* Consequently $\mathrm{Var}(R_n^2/\rho^2)=\frac{1+\pi^2/6}{(\log n+\gamma-2)^2}+O(n^{-1})$ with $\gamma$ Euler's constant, so $R_n^2$ is consistent, and

    $$\mathrm{SE}(R_n^2)\approx\sqrt{1+\pi^2/6}\;\frac{R_n^2}{\log n+\gamma-2}\approx\frac{1.626}{\log n-1.423}\,R_n^2 .$$

4. *(Coalescent indices.)* For four tips $i,j,k,l$ sampled without replacement from the standard ($\lambda=1$) Yule $n$-tree, let $\tau^{(n)}_1,\tau^{(n)}_2,\tau^{(n)}_3$ be the times back to the most recent common ancestors of the pairs $(i,j)$, $(i,k)$ and $(l,k)$ (two pairs sharing a tip, and two disjoint pairs). Then $\mathrm{Var}\,\tau^{(n)}_1=\pi^2/6+O(n^{-1}\log^2n)$, $\mathrm{Cov}(\tau^{(n)}_1,\tau^{(n)}_2)=2-\pi^2/6+O(n^{-1}\log^2n)$ and $\mathrm{Cov}(\tau^{(n)}_1,\tau^{(n)}_3)=3-5\pi^2/18+O(n^{-1}\log^2n)$.

## Expansion

Conditionally on the tree, $(n-1)S_n^2/\sigma^2$ is a quadratic form in the shared branch lengths: the covariance of two tips equals the time from the root to their most recent common ancestor, so $\mathbb{E}[S_n^2\mid\text{tree}]$ is $\sigma^2$ times the average pairwise coalescence depth. Averaging over the Yule tree, whose depths are expressed through harmonic numbers, gives the bias factor, which grows like $\log n$ because the tree height does. The variance of $S_n^2$ involves second moments of coalescence times of pairs, triples and quadruples of tips, which converge to the constants in statement 4; combining them gives the limit $1+\pi^2/6$, a non-vanishing variance reflecting the shared deep branches near the root.

## Sources

- Krzysztof Bartoszek and Serik Sagitov, "A consistent estimator of the evolutionary rate", Journal of Theoretical Biology 371 (2015), 69–78, <https://doi.org/10.1016/j.jtbi.2015.01.019>; numbering as in arXiv:1408.5007: Section 2 (estimator, Eq. (1); Theorem 2.1; standard-error formula, Eq. (2)) and Proposition 3.1.
