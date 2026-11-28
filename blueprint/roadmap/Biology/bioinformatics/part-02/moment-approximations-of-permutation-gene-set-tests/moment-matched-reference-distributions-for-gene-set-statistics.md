# Moment-matched reference distributions for linear and quadratic gene-set statistics

**Statistics.** For a gene set $G$ with weights $w_g$ and gene-level covariances $\hat\beta_g$ as in [permutation moments of gene-level covariance statistics](permutation-moments-of-gene-level-covariance-statistics.md), define

$$\hat T_{G,w} = \sum_{g\in G} w_g\hat\beta_g,\qquad \hat C_{G,w} = \sum_{g\in G} w_g\hat\beta_g^2\quad (w_g \ge 0 \text{ for } C).$$

The self-contained null is that $Y$ is independent of $(X_g)_{g\in G}$. Under permutation of $Y$ (tilde quantities),

$$\mathbb{E}\tilde T = 0,\quad \operatorname{var}\tilde T = \sum_{g,h\in G} w_gw_h\operatorname{cov}(\tilde\beta_g,\tilde\beta_h),\quad \mathbb{E}\tilde C = \sum_{g} w_g\,\mathbb{E}\tilde\beta_g^2,\quad \operatorname{var}\tilde C = \sum_{g,h} w_gw_h\operatorname{cov}(\tilde\beta_g^2,\tilde\beta_h^2).$$

**Linear statistic.** Either use $N(0,\operatorname{var}\tilde T)$, or a scaled beta $A + (B-A)\,\mathrm{Beta}(\alpha,\beta)$ that matches the permutation minimum, maximum, mean and variance:

$$A = \min_\pi \tfrac1n\sum_i\sum_{g} w_gX_{gi}Y_{\pi(i)},\quad B = \max_\pi \tfrac1n\sum_i\sum_{g} w_gX_{gi}Y_{\pi(i)},$$

$$\alpha = \frac{A}{B-A}\Big(\frac{AB}{\operatorname{var}\tilde T} + 1\Big),\qquad \beta = -\frac{B}{B-A}\Big(\frac{AB}{\operatorname{var}\tilde T}+1\Big).$$

Here $A<0<B$, and the parameters are valid when $\operatorname{var}\tilde T < -AB$, which holds except in degenerate cases by the Bhatia-Davis inequality $\operatorname{var} \le -AB$. The extrema are found by sorting. The left p-value is $\mathbb{P}\{\mathrm{Beta}(\alpha,\beta) \le (\hat T - A)/(B-A)\}$, optionally shrunk to $\varepsilon + (1-2\varepsilon)p_L$ with $\varepsilon = \prod_k n_k!/n!$ the smallest attainable permutation p-value when $Y$ takes $K$ distinct values $n_1,\dots,n_K$ times.

**Quadratic statistic.** Use $\sigma^2\chi^2_{(\nu)}$ with

$$\nu = \frac{2(\mathbb{E}\tilde C)^2}{\operatorname{var}\tilde C},\qquad \sigma^2 = \frac{\mathbb{E}\tilde C}{\nu} = \frac{\operatorname{var}\tilde C}{2\,\mathbb{E}\tilde C},$$

and report $\mathbb{P}\{\sigma^2\chi^2_{(\nu)} \ge \hat C\}$.

## Depends on

- [Permutation moments of gene-level covariance statistics](permutation-moments-of-gene-level-covariance-statistics.md)

## Expansion

All moments are exact permutation moments, so no permutations are drawn: the approximation removes the cost, Monte Carlo noise and granularity of permutation p-values. Matching the support $[A,B]$, rather than fitting a Pearson curve by four moments, keeps the observed statistic inside the reference support. The scaled $\chi^2$ is a gamma law fitted by its first two moments, $\mathbb{E} = \sigma^2\nu$ and $\operatorname{var} = 2\sigma^4\nu$. When $X$ and $Y$ are standardized, $\hat T$ with equal weights is the mean gene-phenotype correlation and approximates the sum of per-gene $t$-statistics, since $t_g \approx \sqrt{n-2}\,(\hat\rho_g + \hat\rho_g^3/2)$. On 6,303 curated and GO gene sets in Parkinson's disease expression data the moment p-values closely tracked p-values from up to 999,999 permutations. Rotation sampling gives the same $\mathbb{E}\tilde T$, $\operatorname{var}\tilde T$ and $\mathbb{E}\tilde C$, while $\operatorname{var}\tilde C$ depends on the rotation.

## Sources

- Larson JL, Owen AB. Moment based gene set tests. *BMC Bioinformatics* 16:132 (2015), Eqs. 2-5 and the sections on moment based reference distributions and rotation moments. <https://doi.org/10.1186/s12859-015-0571-7>. PMCID: PMC4419444.
