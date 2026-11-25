# Covariance induced by population stratification

Let $K$ be a finite population label with probabilities $w_k$, and let
$G\in\{0,1,2\}$ and $Y$ be genotype count and phenotype. Assume
$\mathbb E|Y|<\infty$, $\mathbb E[G\mid K=k]=2p_k$,
$\mathbb E[Y\mid K=k]=\mu_k$ and
$\operatorname{Cov}(G,Y\mid K=k)=0$ for positive-weight labels.
Write $\bar p=\sum_kw_kp_k$ and $\bar\mu=\sum_kw_k\mu_k$. Then

$$\operatorname{Cov}(G,Y)=
\sum_kw_k(2p_k-2\bar p)(\mu_k-\bar\mu).$$

Within-group independence is sufficient but stronger than the zero
conditional covariance used here. For one group the result is zero.
For two groups with weight $w$ on the first, it is
$2w(1-w)(p_1-p_2)(\mu_1-\mu_2)$.
For instance $w=1/2$, $p_1=1/4$, $p_2=3/4$,
$\mu_1=0$, $\mu_2=1$ give covariance $1/4$.

## Background

- [A fixed-shift stratified phenotype model](pheno-strat.md)

## Expansion

Expand $\mathbb E[GY]=\sum_kw_k\mathbb E[GY\mid K=k]
=\sum_kw_k(2p_k)\mu_k$ and subtract the product of the two means.
The fixed-shift model is a related special case, not a premise for this
arbitrary finite-mixture identity. No additional graph prerequisite is
needed for the displayed finite conditioning calculation.

For iid subjects the sample covariance converges to this covariance.
If it is nonzero, a test rejecting when its absolute value exceeds a
threshold tending to zero in probability rejects with probability tending
to one. This covers a specified consistent covariance test, not every
unspecified association procedure. With $\mathbb E Y^2<\infty$, ordinary
positive, consistent standard-error scaling is one such construction.
Such a rejection detects a real **marginal** association; interpreting it
as a within-population or causal effect is the confounding error.
Zero covariance alone does not assert within-population independence.

## Sources

- A. L. Price, N. J. Patterson, R. M. Plenge, M. E. Weinblatt, N. A. Shadick and D. Reich, "Principal components analysis corrects for stratification in genome-wide association studies", Nature Genetics 38 (2006), 904–909, <https://doi.org/10.1038/ng1847>.
- B. Devlin and K. Roeder, "Genomic control for association studies", Biometrics 55 (1999), 997–1004, <https://doi.org/10.1111/j.0006-341X.1999.00997.x>. The identity is derived above.
