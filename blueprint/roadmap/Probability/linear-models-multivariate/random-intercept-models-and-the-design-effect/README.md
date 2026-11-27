# Random-intercept models and the design effect

## The random-intercept model and its summary quantities

- [Random-intercept covariance kernel](ri-cov.md)
- [Random-intercept model of cell values](is-random-intercept.md)
- [Cell-level grand mean](cell-mean.md)
- [Pseudobulk value of a donor](pseudobulk.md)
- [Mean of the pseudobulk values](pseudobulk-mean.md)
- [True variance of the cell-level mean](true-var.md)
- [Naive independent-cell variance of the mean](naive-var.md)
- [Intraclass correlation](icc.md)

## Covariance of cells within and across donors

- [Per-cell variance in the random-intercept model](variance-cell.md)
- [Two cells of one donor have covariance the donor variance](covariance-same-donor.md)
- [Cells of different donors are uncorrelated](covariance-other-donor.md)
- [With nonzero donor variance cells of one donor are dependent](not-indep-fun-same-donor.md)
- [Row sums of the random-intercept kernel](sum-ri-cov-right.md)
- [Variance of the cell-level mean](variance-cell-mean.md)

## Naive versus true variance

- [Shortfall of the naive variance](true-var-sub-naive-var.md)
- [Pseudoreplication understates the variance at positive donor variance](naive-var-lt-true-var.md)
- [Naive variance is exact iff no donor variance or one cell per donor](naive-var-eq-true-var-iff.md)
- [Design effect relates the true and naive variances](true-var-eq-design-effect-mul-naive-var.md)

## The per-cell variances do not determine the variance of the mean

- [The independence model reproduces the naive formula](variance-cell-mean-eq-naive-var.md)
- [Equal per-cell variance, equal precision iff equal donor variance](variance-cell-mean-eq-iff.md)

## Pseudobulk values as donor-level replicates

- [Pseudobulk values are uncorrelated replicates](covariance-pseudobulk.md)
- [The mean of the pseudobulk values is the cell-level mean](pseudobulk-mean-eq-cell-mean.md)
- [The replicate formula is exact for pseudobulk](variance-pseudobulk-mean.md)

## Donor-effect decomposition and an explicit Gaussian realization

- [A donor effect plus residual decomposition is a random-intercept model](is-random-intercept-of-decomp.md)
- [Sample space of the Gaussian realization](noise-space.md)
- [Independent standard Gaussian coordinates](std-gaussian-pi.md)
- [Explicit Gaussian random-intercept model](ri-model.md)
- [The Gaussian model is a random-intercept model](is-random-intercept-ri-model.md)
- [Pseudoreplication counterexample](pseudoreplication-counterexample.md)

## Batch perfectly confounded with condition

- [Donor-level mean with condition and batch effects](mean-fn.md)
- [Observed cell values](obs.md)
- [Law of the cell-level data](data-law.md)
- [The observation vector is almost everywhere measurable](aemeasurable-obs.md)
- [Perfect confounding trades batch effect for condition effect](obs-shift-of-confounded.md)
- [Under perfect confounding shifted parameters give the same data law](data-law-shift-of-confounded.md)
- [Under perfect confounding the condition effect is not identifiable](not-identifiable-of-confounded.md)
- [Under perfect confounding no estimator is unbiased for the effect](no-unbiased-estimator-of-confounded.md)
- [What the contrast estimates under confounding](contrast-of-confounded.md)
- [A same-batch donor pair identifies the condition effect](contrast-of-same-batch.md)

## Crossed random intercepts

- [Design matrix of crossed random intercepts](crossed-design.md)
- [Diagonal covariance of crossed random intercepts](crossed-cov.md)
- [Crossed covariance is positive semidefinite for nonnegative components](pos-semidef-crossed-cov.md)
- [Entries of Z G Zᵀ + σ_e² I for crossed random intercepts](phen-cov-crossed-apply.md)
- [Covariances of the Gaussian crossed random-intercept response](covariance-crossed-response.md)
- [Variance of a linear combination of the Gaussian crossed response](variance-contrast-crossed-response.md)

## A single cluster and the design effect

- [All-ones design of a single cluster](cluster-design.md)
- [Entries of σ_c² Z Zᵀ + σ_w² I for a single cluster](phen-cov-cluster-apply.md)
- [The Gaussian cluster response is a random-intercept model](is-random-intercept-cluster-response.md)
- [Variance of each observation of a Gaussian single-cluster response](variance-cluster-row.md)
- [Variance of the mean of a nonempty Gaussian cluster](variance-cluster-mean.md)
- [Cluster-mean variance as design effect times independent-row variance](variance-cluster-mean-eq-design-effect.md)
- [For m ≥ 2 and positive shared variance, naive mean variance is too low](variance-cluster-row-div-lt-mean.md)
- [A nonempty cluster mean has variance at least the shared variance](le-variance-cluster-mean.md)

## Related topics

- [Linear mixed models and BLUP](../../../Biology/quantitative-genetics/linear-mixed-models-and-blup/README.md): the Gaussian mixed model, the marginal and conditional laws of its response, and BLUP as a conditional expectation.
