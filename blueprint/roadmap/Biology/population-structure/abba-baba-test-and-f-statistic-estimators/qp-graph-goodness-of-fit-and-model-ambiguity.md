# Goodness of fit of a qpGraph model and its limits

Let $n\ge2$ populations be given, one of them a base population $O$, and let $\hat f\in\mathbb R^q$, $q=\binom n2$, be the vector of basis f-statistics $f_3(O;X_i,X_j)$ over the $q$ index pairs $1\le i\le j\le n-1$ of the other populations $X_1,\ldots,X_{n-1}$; each is the basis $f_4$-statistic $f_4(O,X_i;O,X_j)$. Fix an admixture-graph topology and its admixture proportions, so that the expected basis vector is linear in the drift lengths $\ell\in\mathbb R^p$: it equals $B\ell$ for the qpGraph [design matrix](../fitting-admixture-graphs-by-least-squares/design-matrix.md) $B\in\mathbb R^{q\times p}$ of full column rank $p<q$. Let $Q$ be a positive definite $q\times q$ matrix and $S_1(g)=-\frac12(g-\hat f)^{\mathsf T}Q^{-1}(g-\hat f)$ the [qpGraph score](../fitting-admixture-graphs-by-least-squares/score-s1.md).

**Exact Gaussian core.** If $\hat f\sim\mathcal N(B\ell_0,Q)$ for some $\ell_0\in\mathbb R^p$, then

$$-2\max_{\ell\in\mathbb R^p}S_1(B\ell)=\min_{\ell\in\mathbb R^p}(\hat f-B\ell)^{\mathsf T}Q^{-1}(\hat f-B\ell)\sim\chi^2_{q-p},$$

the [chi-square law of the Gaussian projection statistic](../../../Probability/linear-models-multivariate/chi-square-law-of-gaussian-projection-residuals/map-gauss-proj-stat-multivariate-gaussia.md) with $V=Q$, $T=\operatorname{range}B$ and codimension $q-\operatorname{rank}B=q-p$. The maximum is over all real $\ell$; when the nonnegativity constraint $\ell\ge0$ of qpGraph is active at the optimum, the constrained statistic is not covered and is in general not chi-square. The admixture proportions are held fixed: optimizing them as well makes the model nonlinear and is outside this statement.

**Asymptotic version.** If $\sqrt L(\hat f_L-B\ell_0)\to\mathcal N(0,V)$ in distribution with $V$ positive definite, and $\hat Q_L$ are covariance estimates with $L\hat Q_L\to V$ in probability, then the statistic computed with $Q=\hat Q_L$ converges in distribution to $\chi^2_{q-p}$.

**Model ambiguity.** A good fit does not identify the graph: two drift models that are [f-equivalent](../centred-population-covariance-and-f-statistics/f-equivalence-classes-of-drift-models.md) have equal f-statistics, hence the same expected basis vector and the same distribution of the fit statistic, even when their topologies differ.

## Depends on

- [Chi-square law of the Gaussian projection statistic](../../../Probability/linear-models-multivariate/chi-square-law-of-gaussian-projection-residuals/map-gauss-proj-stat-multivariate-gaussia.md)
- [The qpGraph score S1](../fitting-admixture-graphs-by-least-squares/score-s1.md)
- [qpGraph design matrix of basis f4 statistics](../fitting-admixture-graphs-by-least-squares/design-matrix.md)
- [Which drift models have the f-statistics of a star tree](../centred-population-covariance-and-f-statistics/f-equivalence-classes-of-drift-models.md)

## Proof depends on

- [Asymptotic rank test for qpWave and qpAdm](rank-test-for-qp-wave-qp-adm.md)
- [Basis independence of the qpGraph score S1](../fitting-admixture-graphs-by-least-squares/score-s1-basis-change.md)
- [Multivariate central limit theorem with a constructed limit](../../../Probability/central-limit-theorems/multivariate-central-limit-theorem/exists-tendsto-in-distribution-inv-sqrt.md)
- [Studentization with a consistent covariance estimator](../../../Probability/convergence-of-measures/slutsky-s-theorem-and-the-delta-method/studentization-for-an-explicitly-supplied-depend.md)
- [Jackknife covariance as a scaled sample covariance](../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/jackknife-covariance-estimation/jack-cov-eq.md)
- [Strong consistency of the scaled block jackknife covariance](../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/jackknife-covariance-estimation/ae-tendsto-card-smul-jack-cov.md)

## Expansion

A full proof page must establish the following.

- The identity $-2\max S_1=$ minimum residual quadratic form, and its identification with the Gaussian projection statistic for positive definite $Q$.
- Invariance of the statistic under change of f-statistic basis, from the [basis independence of $S_1$](../fitting-admixture-graphs-by-least-squares/score-s1-basis-change.md).
- The asymptotic version: a multivariate central limit theorem for the genome-wide f-statistics (independent blocks), consistency of the block-jackknife covariance, studentization, and continuity of the projection statistic in $(V,z)$ at positive definite $V$.
- A flagged boundary case: an example in which the constrained optimum has an active nonnegativity constraint and the statistic is not $\chi^2_{q-p}$.
- An example of two f-equivalent drift models with different topologies.

## Sources

- R. Maier, P. Flegontov, O. Flegontova, U. Isildak, P. Changmai, D. Reich, *On the limits of fitting complex models of population history to f-statistics*, eLife 12 (2023), e85492, <https://reich.hms.harvard.edu/sites/reich.hms.harvard.edu/files/inline-files/elife-85492-v2.pdf> (definitions: the score of equation (3) with $k(k+1)/2$ basis $f_3$-statistics for $k$ populations besides the outgroup, block-jackknife covariance, nonnegative drift weights fitted by quadratic programming; many topologies fit equally well).
