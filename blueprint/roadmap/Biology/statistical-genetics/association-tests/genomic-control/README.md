# Genomic control

## The χ²₁ tail

- [Tail of the chi-square law with one degree of freedom](chi-sq-one-tail.md)
- [The χ²₁ tail as a standard normal probability](chi-sq-one-tail-eq-gaussian-real.md)
- [The χ²₁ tail is strictly decreasing on nonnegative thresholds](chi-sq-one-tail-lt-of-lt.md)
- [The χ²₁ tail is nonincreasing](chi-sq-one-tail-antitone.md)
- [The χ²₁ tail is finite](chi-sq-one-tail-ne-top.md)
- [The χ²₁ tail is below one at positive thresholds](chi-sq-one-tail-lt-one.md)
- [Chernoff bound for the χ²₁ tail](chi-sq-one-tail-to-real-le.md)
- [The χ²₁ tail at 10 is at most 0.05](chi-sq-one-tail-to-real-ten-le.md)

## Genomic-control p-values

- [Genomic-control p-value](gc-pvalue.md)
- [With λ > 0 the genomic-control p-value is nonincreasing](gc-pvalue-antitone.md)
- [With λ > 0 a positive statistic has p-value below one](gc-pvalue-lt-one.md)

## Rejection probability of a rescaled Gaussian score

- [Tail of a centred Gaussian square divided by a positive constant](measure-reject-eq-chi-sq-one-tail.md)

## Calibration in the common-inflation model

- [Common-inflation model of Gaussian null scores](common-inflation-model.md)
- [The common inflation factor is positive](lam-pos.md)
- [Genomic control is exactly calibrated in the common-inflation model](measure-reject-eq.md)
- [Genomic control has type I error exactly α at a χ²₁ critical value](type-i-eq.md)
- [With λ > 1 the uncorrected test is anti-conservative](chi-sq-one-tail-lt-measure-reject-uncorr.md)
- [The corrected statistic has law χ²₁ in the common-inflation model](has-law-sq-div.md)
- [Genomic-control p-values are valid in the common-inflation model](is-valid-pvalue-gc-pvalue.md)

## Marker-specific inflation

- [Dividing by a positive λ below the null variance is anti-conservative](chi-sq-one-tail-lt-measure-reject-of-lt.md)
- [Dividing by λ above the null variance is conservative](measure-reject-lt-chi-sq-one-tail-of-gt.md)

## Moment calibration in the LD-score model

- [Population genomic-control factor of the LD-score model](lambda-gc.md)
- [Deviation from the genomic-control factor under common stratification](integral-chi-sq-strat-sub-lambda-gc.md)
- [Common stratification, h² = 0: every marker is calibrated in mean](integral-chi-sq-strat-div-lambda-gc-of-n.md)
- [The population genomic-control factor is positive](lambda-gc-pos.md)
- [Common stratification, h² ≠ 0: calibration exactly at mean LD score](integral-chi-sq-strat-div-lambda-gc-eq-o.md)
- [Common stratification, h² ≠ 0: over-correction below mean LD score](integral-chi-sq-strat-div-lambda-gc-lt-o.md)
- [Common stratification, h² ≠ 0: under-correction above mean LD score](one-lt-integral-chi-sq-strat-div-lambda.md)
- [Unequal stratification, h² = 0: no single λ calibrates both markers](not-exists-lambda-calibrates-of-strat-ne.md)

## Related topics

- [Valid p-values and false discovery proportion](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/README.md): genomic control with the estimated factor λ̂, the mean of the squared scores; the λ̂-corrected statistic is never exactly χ²₁-calibrated, and, when the scores are almost surely not all zero, a nondegenerate one forces a negative covariance between two of the corrected statistics.
