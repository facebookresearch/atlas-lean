# Unbiased sample covariance of genotypes

For genotypes $g_i(x)$ of $m$ individuals at SNPs $x$, the sample covariance of SNPs $x$ and $y$ is (Loh et al. 2013, Eq. 5)

$$\hat z(x, y) = \frac{1}{m - 1} \sum_{i=1}^{m} \bigl(g_i(x) - \bar g(x)\bigr)\bigl(g_i(y) - \bar g(y)\bigr),$$

where $\bar g$ is the [sample mean genotype](mean-geno.md), $m - 1$ is computed in the reals, and $x/0 = 0$ (so $\hat z = 0$ for $m = 1$). It is meaningful for $m \ge 2$.

## Sources

- P.-R. Loh, M. Lipson, N. Patterson, P. Moorjani, J. K. Pickrell, D. Reich, B. Berger, *Inferring admixture histories of human populations using linkage disequilibrium*, Genetics 193 (2013), 1233–1254, Eq. 5.
