# Sample coverage and coverage-based haplotype richness estimators

**Setting.** A database holds $n$ haplotypes drawn from a population with $N$ (unknown) haplotype classes of probabilities $p_1,\dots,p_N$. Let $X_i$ be the number of database copies of class $i$, $D$ the number of distinct haplotypes observed, and $f_j$ the number of haplotypes observed exactly $j$ times, so $\sum_j f_j = D$ and $\sum_j jf_j = n$. The **sample coverage** is the total probability of the observed classes,

$$C = \sum_{i=1}^N p_i\,\mathbf 1[X_i > 0].$$

**Estimators.**
1. *(Good–Turing coverage.)* $\hat C = 1 - f_1/n$; equivalently, the probability that the next sampled haplotype is absent from the database is estimated by $f_1/n$.
2. *(Equal-frequency richness.)* If all classes were equally frequent, $\hat N_0 = D/\hat C$.
3. *(Coverage estimators with heterogeneity.)* With $\gamma^2$ the squared coefficient of variation of the $p_i$,

$$\hat N = \frac{D}{\hat C} + \frac{n(1-\hat C)}{\hat C}\,\hat\gamma^2, \qquad \hat\gamma^2 = \max\Big\{\frac{D}{\hat C}\,\frac{\sum_j j(j-1)f_j}{n(n-1)} - 1,\; 0\Big\},$$

which reduces to $\hat N_0$ when frequencies are homogeneous.
4. *(Abundant/rare split.)* Classes seen more than $k$ times (customarily $k = 10$) are treated as certainly sampled: with $D = D_{\mathrm{abun}} + D_{\mathrm{rare}}$, $n_{\mathrm{rare}} = \sum_{j\le k} jf_j$ and $\hat C_{\mathrm{rare}} = 1 - f_1/n_{\mathrm{rare}}$, the equal-frequency estimator becomes $\hat N = D_{\mathrm{abun}} + D_{\mathrm{rare}}/\hat C_{\mathrm{rare}}$, and the heterogeneity term is computed from the rare classes only.

## Depends on

- [The Good–Turing identity for the missing mass](../../../../../../not-yet-classified/good-turing/expect-missing-mass.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

The expected missing mass $E[1-C] = \sum_i p_i(1-p_i)^n$ is close to $E[f_1]/n = \sum_i p_i(1-p_i)^{n-1}$, which justifies $\hat C$ even without equal frequencies, with accuracy improving as $f_1$ grows. Dividing $D$ by the coverage scales up the observed classes to the population when each class carries the same mass; heterogeneous frequencies leave more classes unseen than this predicts, and the correction term inflates the estimate in proportion to $\gamma^2$ and to the uncovered fraction. Restricting the correction to rare classes stabilizes it, since abundant haplotypes contribute nothing to the unseen mass but dominate the moment estimate of $\gamma^2$. In forensic practice, $1-\hat C$ quantifies how often a new case haplotype will be absent from the database.

## Sources

- T. Egeland, A. Salas, "Estimating haplotype frequency and coverage of databases", PLoS ONE 3(12) (2008) e3988, Analysis (review of methods related to database coverage), Eqs (1)–(3), (5) and (8), following Good (1953) and Chao and Lee (1992), <https://doi.org/10.1371/journal.pone.0003988>, PMCID PMC2602601.
