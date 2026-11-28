# Asymptotic rank test for qpWave and qpAdm

Let $L_0,\ldots,L_{a}$ be left populations and $R_0,\ldots,R_{b}$ right populations, $a,b\ge1$, and let $F=\bigl(f_4(L_i,L_0;R_j,R_0)\bigr)_{1\le i\le a,\,1\le j\le b}$ be the [qpWave matrix](f4-matrix.md). By the [qpWave rank bound](rank-f4-matrix-le.md), if every left population is an affine combination of $k+1$ source populations then $\operatorname{rank}F\le k$. Let $\hat F_L$ be the genome-wide estimate of $F$ from $L$ loci.

**Statement.** Assume $\operatorname{rank}F=k$ exactly, with $0\le k<\min(a,b)$; that $\sqrt L\,\operatorname{vec}(\hat F_L-F)\to\mathcal N(0,V)$ in distribution with $V$ positive definite; that $\hat V_L\to V$ in probability; and the regularity hypotheses of the [asymptotic chi-square theorem for minimum-distance rank statistics](../rank-of-the-f4-matrix-of-left-and-right-populati/asymptotic-chi-square-for-minimum-distance-rank.md). Then the minimum-distance rank statistic

$$T_L=L\min_{\operatorname{rank}G\le k}\operatorname{vec}(\hat F_L-G)^{\mathsf T}\hat V_L^{-1}\operatorname{vec}(\hat F_L-G)$$

converges in distribution to $\chi^2_{(a-k)(b-k)}$, that is, $(|L|-1-k)(|R|-1-k)$ degrees of freedom with $|L|=a+1$ and $|R|=b+1$. The statement is asymptotic; no finite-sample exactness is claimed.

A small P-value is evidence against $\operatorname{rank}F\le k$. P-values test a rank hypothesis: ranking candidate qpAdm models by their P-values is not a model-selection procedure, and the best model need not have the largest P-value. Whether $T_L$ is asymptotically equivalent to the statistic implemented in qpWave is a separate question not settled here.

## Depends on

- [qpWave rank bound](rank-f4-matrix-le.md)
- [qpWave matrix of f4-statistics](f4-matrix.md)
- [Asymptotic chi-square for minimum-distance rank statistics (assembly)](../rank-of-the-f4-matrix-of-left-and-right-populati/asymptotic-chi-square-for-minimum-distance-rank.md)

## Proof depends on

- [Eckart–Young theorem in operator norm](../../../Analysis/operator-theory/eigenvalue-inequalities/eckart-young-best-rank-approx-operator-n.md); the unweighted case needs its Frobenius-norm form, that a truncated singular value decomposition is a best rank-$k$ approximation in Frobenius norm
- [Jackknife covariance as a scaled sample covariance](../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/jackknife-covariance-estimation/jack-cov-eq.md)
- [Strong consistency of the scaled block jackknife covariance](../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/jackknife-covariance-estimation/ae-tendsto-card-smul-jack-cov.md)
- [Multivariate central limit theorem with a constructed limit](../../../Probability/central-limit-theorems/multivariate-central-limit-theorem/exists-tendsto-in-distribution-inv-sqrt.md)
- [Studentization with a consistent covariance estimator](../../../Probability/convergence-of-measures/slutsky-s-theorem-and-the-delta-method/studentization-for-an-explicitly-supplied-depend.md)

## Expansion

A full proof page must establish the following.

- The degrees of freedom $(a-k)(b-k)$: the codimension of the manifold of $a\times b$ matrices of rank exactly $k$, which has dimension $k(a+b-k)$.
- The central limit theorem for $\operatorname{vec}\hat F_L$ under independent blocks of loci and the consistency of the block-jackknife covariance estimate.
- The reduction to the minimum-distance theorem, including the unweighted case, where the minimum is attained by the best rank-$k$ approximation (Eckart–Young).
- That no finite-sample exactness follows.

## Sources

- E. Harney, N. Patterson, D. Reich, J. Wakeley, *Assessing the performance of qpAdm: a statistical tool for studying population admixture*, Genetics 217(4) (2021), iyaa045, <https://pmc.ncbi.nlm.nih.gov/articles/PMC8049561/> (definitions; P-value ranking should not be used to identify the best model).
- D. Reich et al., *Reconstructing Native American population history*, Nature 488 (2012), 370–374, <https://ui.adsabs.harvard.edu/abs/2012Natur.488..370R> (background: the qpWave rank test).
