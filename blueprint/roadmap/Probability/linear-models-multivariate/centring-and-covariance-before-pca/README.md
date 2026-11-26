# Centring and covariance before PCA

Throughout, $X$ is a real $n \times p$ data matrix whose rows are $n$ samples and whose columns are
$p$ features, $\bar x \in \mathbb{R}^p$ is its vector of column
[sample means](../principal-component-analysis/col-mean.md)
($0$ when $n = 0$), $X_c = X - \mathbf 1 \bar x^\top$ its
[centred matrix](../principal-component-analysis/center.md)
and $S = (n-1)^{-1} X_c^\top X_c$ its
[sample covariance matrix](../principal-component-analysis/sample-cov.md),
where $(n-1)^{-1}$ is $0$ for $n = 1$ by convention; $S = 0$ for $n \le 1$, since then $X_c = 0$.
The pages compare $S$ with the uncentred second moment $\frac1n X^\top X$, describe its rank and
singularity, and show that in a design where batch and condition are confounded, with $p \ge 1$, no
function of $S$ recovers the batch effect or the biological signal.

## The uncentred second moment and the scatter identity

- [Uncentred second-moment matrix of a data matrix](second-moment.md)
- [Column sums are $n$ times the column means](sum-eq-mul-col-mean.md)
- [The centred data matrix is $X - \mathbf{1}\bar x^\top$](center-eq-sub-vec-mul-vec.md)
- [Scatter matrix of centred data is $X^\top X - n\bar x \bar x^\top$](transpose-center-mul-center.md)
- [Sample covariance times $n - 1$ is $X^\top X - n\bar x\bar x^\top$](sub-one-smul-sample-cov.md)
- [Sample covariance as $(n-1)^{-1}(X^\top X - n\bar x\bar x^\top)$](sample-cov-eq-sub.md)
- [Empirical covariance is the second moment minus the mean outer product](inv-smul-transpose-center-mul-center.md)
- [Sample covariance is $\frac{n}{n-1}$ times the empirical covariance](sample-cov-eq-second-moment.md)
- [Mean-zero data: sample covariance is $n/(n-1)$ times the second moment](sample-cov-eq-smul-second-moment-of-col.md)

## Invariances of the centred covariance

- [With $n \ge 1$ samples, a shift by $c$ shifts the column means by $c$](col-mean-add-vec-mul-vec-one.md)
- [Centring removes a common shift of all samples](center-add-vec-mul-vec-one.md)
- [Sample covariance is invariant under a common shift of all samples](sample-cov-add-vec-mul-vec-one.md)
- [Centring commutes with negation](center-neg.md)
- [Negating the data leaves the sample covariance unchanged](sample-cov-neg.md)

## Rank and singularity

- [Columns of the centred data matrix sum to zero](one-vec-mul-center.md)
- [Centred data matrix has rank at most $n - 1$](rank-center-le.md)
- [With at most one sample, the centred data matrix is zero](center-eq-zero-of-le-one.md)
- [With at most one sample, the sample covariance is zero](sample-cov-eq-zero-of-le-one.md)
- [Sample covariance has the same rank as the centred data matrix](rank-sample-cov.md)
- [Sample covariance has rank at most $n - 1$](rank-sample-cov-le.md)
- [With $n \le p$ and $p \ge 1$, the sample covariance is singular](det-sample-cov-eq-zero-of-le.md)
- [Projecting centred data subtracts the projected mean](center-mul-vec.md)
- [Projections of the samples sum to $n$ times the projected mean](sum-mul-vec.md)
- [Sample covariance and centred data have the same null vectors](sample-cov-mul-vec-eq-zero-iff-center.md)
- [Sample covariance vanishes on $w$ iff samples project equally on it](sample-cov-mul-vec-eq-zero-iff.md)
- [Sample covariance is singular iff samples lie in an affine hyperplane](det-sample-cov-eq-zero-iff.md)
- [$S$ is positive definite iff no affine hyperplane contains all samples](pos-def-sample-cov-iff.md)
- [Centring is multiplication by $I - n^{-1}\mathbf{1}\mathbf{1}^\top$](center-eq-centering-mul.md)
- [Centring does not raise the rank](rank-center-le-rank.md)
- [Centring lowers the rank by at most one](rank-le-rank-center-add-one.md)

## A confounded batch design

- [Additive design with batch and biological effects](batch-model.md)
- [Sample covariance of the additive design does not depend on $\mu$](sample-cov-batch-model-baseline.md)
- [Confounded design: the data depend only on $\beta + \delta$](batch-model-confounded.md)
- [Confounded design: sample covariance depends only on $\beta + \delta$](sample-cov-batch-model-eq-of-add-eq.md)
- [With $p \ge 1$, $S$ does not determine a confounded batch effect](not-exists-batch-estimator.md)
- [With $p \ge 1$, $S$ does not determine a confounded biological signal](not-exists-signal-estimator.md)
- [Centring an outer product $u v^\top$ centres $u$](center-vec-mul-vec.md)
- [$S(u v^\top)$ is the sample variance of $u$ times $v v^\top$](sample-cov-vec-mul-vec.md)
- [Noiseless confounded design: closed form of the sample covariance](sample-cov-batch-model-confounded-noisel.md)
- [Sample covariance of an outer product has rank at most one](rank-sample-cov-vec-mul-vec-le.md)
- [Noiseless confounded design: sample covariance has rank at most one](rank-sample-cov-batch-model-confounded-n.md)
