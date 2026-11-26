# Finite probability: moments, least squares and model-conditional intervals

## A. Expectation and events

- [Expectation under a finite weight](expectation.md)
- [Probability of an event under a finite weight](prob.md)
- [Expectation of a constant](expectation-const.md)
- [Expectation is linear](expectation-linear.md)
- [Expectation of an indicator is the probability of the event](expectation-indicator.md)
- [Total probability for a two-set partition](prob-inter-add-prob-sdiff.md)
- [Law of total probability](sum-prob-filter-eq.md)
- [Normalizing a weight by its total gives total mass one](sum-div-sum-eq-one.md)
- [Expectation under a normalized weight](expectation-div-sum.md)

## B. Variance and covariance

- [Covariance under a finite weight](covariance.md)
- [Variance under a finite weight](variance.md)
- [Variance of an affine transformation](variance-affine.md)
- [Covariance is linear in its first argument](covariance-linear-left.md)
- [Covariance is linear in its second argument](covariance-linear-right.md)
- [Covariance of two linear combinations](covariance-sum-mul-sum.md)
- [Mean of a two-state indicator](expectation-two-state.md)
- [Variance of a two-state indicator](variance-two-state.md)

## C. Covariance matrices

- [Covariance matrix of a finite random vector](cov-matrix.md)
- [Covariance under a linear map](cov-matrix-mul-vec.md)

## D. Product weights and independence

- [Expectation of a product under a product weight](expectation-prod-mul.md)
- [Probabilities of product events under a product weight](prob-prod.md)
- [Independence implies zero covariance](covariance-prod-eq-zero.md)
- [Zero covariance does not imply independence](exists-covariance-eq-zero-prob-ne.md)

## E. Comparison with `PMF` moments

- [Real weights of a probability mass function on a finite type sum to one](sum-to-real-eq-one.md)
- [Integration against a finite PMF is a finite expectation](integral-to-measure-eq-expectation.md)
- [Variance against a finite PMF is a finite variance](variance-to-measure-eq.md)

## F. Sample statistics and i.i.d. samples

- [Sample mean](sample-mean.md)
- [Divide-by-n sample variance](sample-var.md)
- [Divide-by-(n − 1) sample variance](sample-var-unbiased.md)
- [Deviations from the sample mean sum to zero](sum-sub-sample-mean.md)
- [The sample mean as an expectation under the empirical weight](sample-mean-eq-expectation.md)
- [The divide-by-n sample variance as a variance under the empirical weight](sample-var-eq-variance.md)
- [The empirical weight of a nonempty finite index set sums to one](sum-inv-card-eq-one.md)
- [Expectation of a product over distinct i.i.d. coordinates](expectation-pi-prod.md)
- [The i.i.d. weight of a finite distribution sums to one](sum-pi-prod-eq-one.md)
- [Each coordinate of an i.i.d. sample has the common law](expectation-pi-eval.md)
- [Expectation of a product of two distinct i.i.d. coordinates](expectation-pi-eval-mul-eval.md)
- [Expectation of the sample mean of an i.i.d. sample](expectation-sample-mean.md)
- [Bessel's correction](expectation-sample-var-unbiased.md)

## G. Least squares for a line

- [Centred cross-product sum](sxy.md)
- [Least-squares slope](ols-slope.md)
- [Least-squares intercept](ols-intercept.md)
- [Residual sum of squares of a line](rss-line.md)
- [Cross-product sum as a raw sum minus the product of means](sxy-eq-sum-mul-sub.md)
- [Least-squares residuals sum to zero](sum-resid-ols.md)
- [Least-squares residuals are orthogonal to the regressor](sum-mul-resid-ols.md)
- [Normal equations](normal-equations-iff.md)
- [Least-squares residuals are orthogonal to the centred regressor](sum-sub-sample-mean-mul-resid-ols.md)
- [Decomposition of the residual sum of squares around the least-squares line](rss-line-eq-rss-line-ols-add.md)
- [The least-squares line minimizes the residual sum of squares](rss-line-ols-le.md)
- [Least squares is not unique for a constant regressor](rss-line-shift-eq-of-sxy-self-eq-zero.md)
- [Unique least-squares line](ols-unique-minimizer-iff.md)

## Least squares is linear in the responses

- [Cross-product sum with centred first argument](sxy-eq-sum-sub-mul.md)
- [Least-squares slope of exactly affine responses](ols-slope-affine.md)
- [The sample mean is affine](sample-mean-affine.md)
- [Least-squares intercept of exactly affine responses](ols-intercept-affine.md)
- [The least-squares slope of integrable responses is integrable](integrable-ols-slope.md)
- [Expectation of the least-squares slope](integral-ols-slope.md)
- [Expectation of the least-squares intercept](integral-ols-intercept.md)

## H. Least squares in matrix form

- [Least-squares residuals are orthogonal to the columns of the design matrix](transpose-mul-vec-sub-ols-estimator.md)
- [Invertibility of the Gram matrix and linear independence of the columns](is-unit-transpose-mul-self-iff.md)
- [Design matrix of the simple linear model](design-matrix.md)
- [Determinant of the Gram matrix of the simple linear model](det-gram-design-matrix.md)
- [Full column rank of the simple linear model](is-unit-gram-design-matrix-iff.md)
- [Matrix least squares for the simple linear model](ols-estimator-design-matrix.md)

## I. Intervals under a sampling model

- [Interval from a pivot](pivot-interval.md)
- [Pivot inversion for an interval](mem-pivot-interval-iff.md)
- [Coverage under a sampling model](measure-mem-pivot-interval.md)
- [The standardized pivot of a normal statistic is standard normal](has-law-pivot-of-has-law-gaussian-real.md)
- [Known-variance normal location model](measure-mem-z-interval.md)
- [Credible interval under a finite posterior](is-credible-interval.md)
- [Posterior coverage of a credible interval](expectation-indicator-eq.md)

## J. Conditioning on an event of positive mass

- [Weights conditioned on an event of positive probability](cond-weights.md)
- [Normalization](cond-weights-is-distribution.md)
- [Ratio identity](prob-cond-weights.md)
- [Positive mass](prob-pos-iff-nonempty.md)
- [Cauchy-Schwarz for finite covariance](covariance-sq-le-variance-mul-variance.md)
- [Covariance under a finite probability mass function](covariance-to-measure-eq.md)
- [Normal equations, matrix form](gram-mul-vec-ols-estimator.md)
- [Uniqueness of the OLS solution under full rank](eq-ols-estimator-iff.md)
