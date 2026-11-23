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

## Estimating the inflation factor from the scan

- [Mean-based estimate of the genomic-control factor](lambda-hat.md)
- [Genomic-control statistic with the estimated factor λ̂](gc-stat.md)
- [The mean-based estimate λ̂ is nonnegative](lambda-hat-nonneg.md)
- [The estimated-factor statistic is nonnegative](gc-stat-nonneg.md)
- [Closed form of the estimated-factor statistic](gc-stat-eq.md)
- [The estimated-factor statistic never exceeds the number of genes](gc-stat-le-card.md)
- [With some score nonzero, the λ̂-corrected statistics sum to m](sum-gc-stat.md)
- [Raising another gene's statistic lowers Tⱼ when zⱼ ≠ 0](gc-stat-update-lt.md)

## Further properties of the χ²₁ tail and its real-valued form

- [The χ²₁ tail is positive at every nonnegative threshold](chi-sq-one-tail-pos.md)
- [The χ²₁ tail as a real-valued function](chi-sq-one-tail-real.md)
- [The real-valued χ²₁ tail is nonincreasing](antitone-chi-sq-one-tail-real.md)
- [The real-valued χ²₁ tail is strictly decreasing for c ≥ 0](chi-sq-one-tail-real-lt-of-lt.md)
- [The real and extended-real χ²₁ tails agree](of-real-chi-sq-one-tail-real.md)

## Exact calibration with λ̂ is impossible

- [Estimated-factor statistics of random scores](gc-stat-rv.md)
- [Measurable scores give measurable λ̂-corrected statistics](measurable-gc-stat-rv.md)
- [The λ̂-corrected test never rejects at a threshold c ≥ m](measure-lt-gc-stat-rv-eq-zero.md)
- [Strictly conservative against χ²₁ at every threshold c ≥ m](measure-lt-gc-stat-rv-lt-chi-sq-one-tail.md)
- [Calibrated with the true λ, strictly conservative with λ̂ at c ≥ m](calibrated-true-and-not-calibrated-estim.md)
- [The λ̂-corrected statistic is never exactly χ²₁-calibrated](not-forall-measure-lt-gc-stat-rv-eq.md)

## Tail calibration of the λ̂ family

- [The λ̂ family is tail-calibrated iff its null tails lie below χ²₁](is-tail-calibrated-family-gc-stat-rv-iff.md)
- [Bonferroni bound for the λ̂ tests under arbitrary dependence](measure-exists-le-gc-stat-rv-le.md)
- [The χ²₁ tail integrates to 1 over the positive half-line](lintegral-chi-sq-one-tail.md)
- [A tail-calibrated λ̂-corrected statistic has integral below 1](lintegral-gc-stat-rv-lt-one.md)
- [For an a.s. nonzero score vector the λ̂-corrected means sum to m](sum-lintegral-gc-stat-rv.md)
- [Global null: tail calibration fails when scores are a.s. not all zero](not-is-tail-calibrated-family-gc-stat-rv.md)

## Calibration with a general random estimate of λ

- [Upper tail bound for Z²/L when L ≥ κλ on a set E](measure-lt-div-le-chi-sq-one-tail-add.md)
- [Lower tail bound for Z²/L when 0 < L ≤ κλ on a set E](chi-sq-one-tail-le-measure-lt-div-add.md)
- [An estimate always below κλ with κ < 1 is strictly anti-conservative](chi-sq-one-tail-lt-measure-lt-div-of-le.md)
- [An estimate always above κλ with κ > 1 is strictly conservative](measure-lt-div-lt-chi-sq-one-tail-of-mul.md)

## Negative coupling and failure of PRDS

- [The λ̂-corrected statistics are square integrable](mem-lp-gc-stat-rv.md)
- [For an a.s. nonzero score vector the covariances sum to zero](sum-sum-covariance-gc-stat-rv.md)
- [A nondegenerate λ̂-corrected statistic forces a negative covariance](exists-covariance-gc-stat-rv-neg.md)
- [Equal pairwise covariances of λ̂-corrected statistics are −v/(m − 1)](covariance-gc-stat-rv-eq-of-forall-eq.md)
- [With two genes and a nonzero score vector, T₀ + T₁ = 2](gc-stat-two-add.md)
- [Two-gene λ̂ p-values are not PRDS when T₀ falls on both sides of 1](not-is-prdson-tail-pvalue-gc-stat-rv-two.md)

## Two independent Gaussian null genes

- [The χ²₁ tail at 1 is below one half](chi-sq-one-tail-one-lt-half.md)
- [With two genes and a nonzero score vector, T₀ ≥ 1 iff z₁² ≤ z₀²](one-le-gc-stat-two-iff.md)
- [Two-gene common-inflation model: the scores are a.s. not both zero](ae-sum-sq-ne-zero.md)
- [Two independent 𝒩(0, λ) null scores give P(T₀ ≥ 1) ≥ 1/2](half-le-measure-one-le-gc-stat-rv-two.md)
- [Two independent 𝒩(0, λ) null scores give P(T₀ < 1) ≥ 1/2](half-le-measure-gc-stat-rv-two-lt-one.md)
- [Two independent null genes: the λ̂ test is anti-conservative at 1](chi-sq-one-tail-lt-measure-one-le-gc-sta.md)
- [Two independent null genes: the λ̂ family is not tail-calibrated](not-is-tail-calibrated-family-gc-stat-rv-2.md)
- [Two independent null genes: the λ̂ p-values are not PRDS](not-is-prdson-tail-pvalue-gc-stat-rv-two-2.md)
- [Two independent null genes: T₀ has positive variance](variance-gc-stat-rv-two-pos.md)
- [Two independent null genes: T₀ and T₁ have negative covariance](covariance-gc-stat-rv-two-neg.md)
