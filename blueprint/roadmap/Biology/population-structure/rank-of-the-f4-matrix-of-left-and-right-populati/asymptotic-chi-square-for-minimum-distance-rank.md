# Asymptotic chi-square for minimum-distance rank statistics (assembly)

Let $F$ be a real $n\times r$ matrix, $0\le k<\min(n,r)$, and for each $L$ let $\widehat F_L$ be a random $n\times r$ matrix and $\widehat V_L$ a random symmetric $nr\times nr$ matrix. Assume

- $\operatorname{rank}F=k$ exactly;
- $\sqrt L\,\operatorname{vec}(\widehat F_L-F)\to\mathcal N(0,V)$ in distribution, with $V$ positive definite;
- $\widehat V_L\to V$ in probability.

Define the minimum-distance rank statistic

$$D_L=L\min_{\operatorname{rank}G\le k}\operatorname{vec}(\widehat F_L-G)^{\mathsf T}\,\widehat V_L^{-1}\,\operatorname{vec}(\widehat F_L-G),$$

with $\widehat V_L^{-1}$ replaced by any fixed matrix on the event, of probability tending to $0$, that $\widehat V_L$ is singular. Then $D_L\to\chi^2_{(n-k)(r-k)}$ in distribution. The statement is the deterministic reduction: the central limit theorem and the consistent covariance estimator are hypotheses. Near $F$, the set $\{\operatorname{rank}G\le k\}$ is a smooth manifold of codimension $(n-k)(r-k)$ ([local manifold structure](local-manifold-structure-of-rank-k-matrices.md)); by the [local quadratic approximation of the distance](local-quadratic-approximation-of-the-distance-to.md), $D_L$ differs by $o_P(1)$ from the [Gaussian projection statistic](../../../Probability/linear-models-multivariate/chi-square-law-of-gaussian-projection-residuals/gauss-proj-stat.md) of $\sqrt L\operatorname{vec}(\widehat F_L-F)$ onto the tangent space, whose limit law is the [chi-square law](../../../Probability/linear-models-multivariate/chi-square-law-of-gaussian-projection-residuals/map-gauss-proj-stat-multivariate-gaussia.md) with $(n-k)(r-k)$ degrees of freedom, by continuous mapping.

## Depends on

- [Local manifold structure of rank-k matrices](local-manifold-structure-of-rank-k-matrices.md)
- [Local quadratic approximation of the distance to a smooth submanifold](local-quadratic-approximation-of-the-distance-to.md)
- [Chi-square law of the Gaussian projection statistic](../../../Probability/linear-models-multivariate/chi-square-law-of-gaussian-projection-residuals/map-gauss-proj-stat-multivariate-gaussia.md)

## Proof depends on

- [Continuous mapping theorem, integral form](../../../Probability/convergence-of-measures/continuous-mapping-theorem/continuous-mapping.md)
- [Studentization with a consistent covariance estimator](../../../Probability/convergence-of-measures/slutsky-s-theorem-and-the-delta-method/studentization-for-an-explicitly-supplied-depend.md)

## Expansion

A proof page must establish:

- that the minimum over the closed set $\{\operatorname{rank}G\le k\}$ is attained and, with probability tending to $1$, by a matrix near $F$;
- the replacement of $\widehat V_L^{-1}$ by $V^{-1}$, which needs the quadratic approximation uniformly for weight matrices in a compact neighbourhood of $V^{-1}$;
- the continuous-mapping step from the Gaussian limit to the projection statistic;
- the special case $k=0$, where the constraint set is $\{0\}$ and $D_L$ is the Wald statistic $L\operatorname{vec}(\widehat F_L)^{\mathsf T}\widehat V_L^{-1}\operatorname{vec}(\widehat F_L)$ with $nr$ degrees of freedom (here $F=0$);
- consistency: if $\operatorname{rank}F>k$ under the same hypotheses, then $D_L\to\infty$ in probability, since the minimum distance converges to a positive constant.

## Sources

- E. Harney, N. Patterson, D. Reich and J. Wakeley, *Assessing the performance of qpAdm: a statistical tool for studying population admixture*, Genetics 217(4) (2021), iyaa045, <https://pmc.ncbi.nlm.nih.gov/articles/PMC8049561/> (qpAdm rank testing and P-value calibration; background).
- D. Reich et al., *Reconstructing Native American population history*, Nature 488 (2012), 370–374, <https://ui.adsabs.harvard.edu/abs/2012Natur.488..370R> (qpWave rank test; background).
