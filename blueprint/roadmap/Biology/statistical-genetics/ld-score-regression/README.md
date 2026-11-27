# LD-score regression

## LD scores of a genotype matrix

- [Normalized cross product of genotype markers](ld-corr.md)
- [LD score of a marker](ld-score.md)
- [Standardized genotype matrix](is-standardized.md)
- [A standardized marker has correlation one with itself](ld-corr-self.md)
- [The LD score of a standardized marker is at least one](one-le-ld-score.md)
- [Squared correlations of standardized markers are at most one](ld-corr-sq-le-one.md)
- [Mean LD score](mean-ldscore.md)

## The random-effects model and its association statistics

- [Random-effects model of LD-score regression](model.md)
- [Nonnegativity of heritability in the LD-score model](h2-nonneg.md)
- [Heritability is at most one in the LD-score model](h2-le-one.md)
- [Phenotype in the LD-score model](pheno.md)
- [Normalized marginal score in the LD-score model](beta-hat.md)
- [Association statistic in the LD-score model](chi-sq.md)
- [Expected association statistic for an arbitrary genotype matrix](integral-chi-sq.md)
- [LD-score regression](integral-chi-sq-of-standardized.md)
- [Polygenic inflation of the mean association statistic](mean-integral-chi-sq.md)

## Population stratification and confounding

- [Phenotype with population stratification](pheno-strat.md)
- [Normalized score under stratification](beta-hat-strat.md)
- [Association statistic under stratification](chi-sq-strat.md)
- [Expected association statistic under stratification](integral-chi-sq-strat.md)
- [Expected statistic under stratification for standardized genotypes](integral-chi-sq-strat-of-standardized.md)
- [LD-score regression with constant stratification](integral-chi-sq-strat-of-const.md)
- [Mean association statistic with constant stratification](mean-integral-chi-sq-strat-of-const.md)
- [Attenuation ratio](attenuation-ratio.md)
- [Attenuation ratio under constant stratification](attenuation-ratio-of-const.md)
- [Confounding share of inflation under constant stratification](confounding-share-of-const.md)
- [Confounding share lies between 0 and 1](confounding-share-mem-icc.md)
- [Covariance induced by population stratification](population-stratification-creates-spurious-assoc.md)

## The regression identity and the unweighted estimator

- [LD-score regression identity](integral-chi-sq-strat-eq.md)
- [The published regression equation holds exactly if and only if h² = 0](integral-chi-sq-strat-eq-paper-iff.md)
- [Unweighted LD-score regression estimator of heritability](ols-h2-hat.md)
- [Exact recovery of h² from statistics affine in the LD scores](ols-h2-hat-affine.md)
- [The association statistic under stratification is integrable](integrable-chi-sq-strat.md)
- [Population consistency of the unweighted estimator](ols-h2-hat-integral-chi-sq-strat.md)
- [Unbiasedness of the unweighted LD-score regression estimator](integral-ols-h2-hat-chi-sq-strat.md)
- [The unweighted LD-score regression estimator is integrable](integrable-ols-h2-hat-chi-sq-strat.md)
- [The intercept measures confounding](integral-ols-intercept-chi-sq-strat.md)
- [Consistency of the unweighted LD-score regression estimator](tendsto-in-measure-ols-h2-hat.md)

## Variance of the least-squares slope and of the estimator

- [Row-sum bound for a quadratic form](sum-mul-mul-le-of-row-sum.md)
- [Variance of a linear combination as a quadratic form](variance-fun-sum-mul-eq.md)
- [Variance of a linear combination under a covariance row-sum bound](variance-fun-sum-mul-le.md)
- [The least-squares slope is linear in the responses](ols-slope-eq-sum.md)
- [The squared least-squares weights sum to the reciprocal spread](sum-ols-weight-sq.md)
- [Variance of the least-squares slope](variance-ols-slope-le.md)
- [Variance bound for the LD-score regression estimator](variance-h2-hat-le.md)
- [The LD-score regression estimator is square integrable](mem-lp-h2-hat.md)
- [The deterministic rate of the variance bound](sq-div-mul-div-le.md)
- [M / N² tends to 0 when N grows at least linearly in M](tendsto-div-sq-of-le.md)
- [Vanishing estimator variance under bounded covariance row sums](tendsto-variance-h2-hat-of-row-sum.md)

## The LD-block dependence model

- [LD-block dependence model](ldblock-model.md)
- [Twice a covariance is at most the sum of the variances](two-mul-abs-covariance-le.md)
- [Covariances under an LD-block model are bounded by the variance bound](abs-covariance-le.md)
- [Bounded LD gives bounded covariance row sums](sum-abs-covariance-le.md)
- [The variance bound of an LD-block model is nonnegative](nonneg.md)
- [Vanishing estimator variance under an LD-block model as M grows](tendsto-variance-h2-hat-of-ld-block.md)
- [Vanishing estimator variance for association statistics in LD blocks](tendsto-evariance-h2-hat-chi-sq-strat.md)

## Vanishing variance from fourth moments of the scores

- [The square of a function in L⁴ is in L²](mem-lp-sq-of-mem-lp-four.md)
- [The variance of a multiple of a square is at most its second moment](variance-sq-le-integral.md)
- [Score-level LD-block model](score-block-model.md)
- [A score-level model gives an LD-block model for scaled squared scores](to-ldblock-model.md)
- [Bounded LD bounds the expected statistic](integral-chi-sq-strat-le.md)
- [LD-block model for the association statistics from fourth moments](ld-block-model-chi-sq-strat.md)
- [Variance bound for the estimator of one design from fourth moments](variance-ols-h2-hat-le-of-fourth-moment.md)
- [Vanishing estimator variance from fourth moments and bounded LD scores](tendsto-variance-ols-h2-hat-of-fourth-mo.md)
- [Consistency of LD-score regression from fourth moments](tendsto-in-measure-ols-h2-hat-of-fourth.md)

## A product probability space for the designs

- [Product measure with independent coordinates of law ν](coord-measure.md)
- [Centred law with unit variance and bounded support](is-bounded-unit-law.md)
- [Almost surely every coordinate is bounded by C in absolute value](ae-abs-coord-le.md)
- [The coordinates are independent under the product measure](i-indep-fun-coord.md)
- [The coordinates are orthonormal in L²](integral-coord-mul.md)
- [The LD-score model on the product space](model-2.md)
- [The model on the product space has heritability h²](model-h2.md)
- [The effects of the product-space model have mean zero](integral-model-beta.md)
- [The noise of the product-space model has mean zero](integral-model-eps.md)
- [Association statistic of the product-space model written out](chi-sq-strat-model.md)

## Block designs

- [Block design of a genotype matrix](block-design.md)
- [Squared genotypes of a block design are at most N](sq-le.md)
- [Markers of different blocks are uncorrelated](ld-corr-eq-zero.md)
- [Bound constant for the statistics of a block design](chi-sq-bound.md)
- [Pointwise bound on the phenotype along a block design](pheno-sq-le.md)
- [Bound on the statistics of a block design at bounded coordinates](chi-sq-strat-mem-icc.md)
- [Coordinates used by an LD block](coord-set.md)
- [The σ-algebra of the coordinates of an LD block](block-sigma.md)
- [The statistic of a marker depends only on the coordinates of its block](measurable-chi-sq-strat-block-sigma.md)
- [Statistics of different blocks are independent](indep-fun-chi-sq-strat.md)
- [The LD-block model holds along a block design](ld-block-model.md)
- [Variance bound for the estimator along a block design](variance-ols-h2-hat-le.md)
- [Replacing λ by its positive part keeps the bound N ≤ λ M](le-max-mul.md)
- [Vanishing estimator variance along a sequence of block designs](tendsto-variance-ols-h2-hat.md)
- [Consistency of LD-score regression along a sequence of block designs](tendsto-in-measure-ols-h2-hat-block-desi.md)

## Replicated designs

- [A sum over b n terms as a double sum over copies and positions](sum-fin-mul.md)
- [Summing a function of the position over all copies](sum-comp-snd.md)
- [Replicated genotype matrix of a template block](replicate.md)
- [The replicated matrix of a standardized template is standardized](is-standardized-replicate.md)
- [Normalized cross products of the replicated matrix](ld-corr-replicate.md)
- [The LD scores of the replicated design](ld-score-replicate.md)
- [The LD-score spread of the replicated design](sxy-ld-score-replicate.md)
- [The replicated block design](replicate-design.md)
- [A template with unequal LD scores has individuals and markers](pos-of-sxy-ld-score.md)
- [Vanishing estimator variance along the replicated designs](tendsto-variance-ols-h2-hat-replicate.md)
- [Consistency of LD-score regression along the replicated designs](tendsto-in-measure-ols-h2-hat-replicate.md)

- [Residual stratification produces covariance between a polygenic score and ancestry](residual-stratification-produces-prs-ancestry-co.md)
- [Effective polygenicity and LD fourth moments](effective-polygenicity-and-ld-fourth-moments/README.md)
- [Expression-mediated heritability](expression-mediated-heritability/README.md)
