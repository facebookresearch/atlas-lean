# Valid p-values and false discovery proportion

- [Valid p-value](is-valid-pvalue.md)
- [Uniform p-values are valid](is-valid-pvalue-of-has-law-uniform.md)
- [Validity from conditional validity with a bounded count](is-valid-pvalue-of-forall-cond.md)
- [Validity from conditional validity](is-valid-pvalue-of-forall-cond-of-ne-zer.md)
- [Number of p-values below a threshold](num-below.md)
- [Number of p-values below a threshold is at most the total](num-below-le.md)
- [Number of p-values below a threshold is monotone](num-below-mono.md)
- [False discovery proportion](false-discovery-proportion.md)
- [False discovery proportion is nonnegative](false-discovery-proportion-nonneg.md)
- [False discovery proportion is at most one](false-discovery-proportion-le-one.md)
- [Rounding a valid p-value up preserves validity](mono-ae.md)
- [Tail bound of a valid p-value](valid-measure-real-le.md)
- [False discovery proportion as a sum over true nulls](fdp-eq-sum.md)
- [Setting a p-value to zero does not decrease the count below a threshold](num-below-update-le.md)
- [Setting a small p-value to zero keeps the count below a threshold](num-below-update-eq.md)
- [Step-up index of a multiple-testing procedure](step-up-index.md)
- [The step-up index is at most m](step-up-index-le.md)
- [At least k* p-values lie below the step-up threshold](step-up-index-le-num-below.md)
- [Maximality of the step-up index](le-step-up-index.md)
- [Exactly k* p-values lie below the step-up threshold](num-below-step-up-index.md)
- [Setting a p-value to zero does not decrease the step-up index](step-up-index-le-update.md)
- [The step-up index is positive once a p-value is zero](one-le-step-up-index-update.md)
- [Replacing a rejected p-value by zero keeps the step-up index](step-up-index-update-eq.md)
- [Leave-one-out property of step-up procedures](step-up-leave-one-out.md)
- [Measurability of the count below a random threshold](measurable-num-below-comp.md)
- [Measurability of the count below a fixed threshold](measurable-num-below.md)
- [Measurability of the step-up index](measurable-step-up-index-comp.md)
- [The step-up index is a qualifying index](step-up-index-mem.md)
- [The step-up index as a finite supremum](step-up-index-eq-sup.md)
- [Upper tail of a measure on the natural numbers](upper-tail.md)
- [Exact upper-tail p-value](upper-tail-pvalue.md)
- [Upper tails decrease with the cutoff](upper-tail-antitone.md)
- [Validity of the upper-tail p-value](is-valid-pvalue-upper-tail-pvalue.md)
- [Exact calibration of the upper-tail p-value at attainable levels](measure-upper-tail-pvalue-le-upper-tail.md)
- [Lower tail of a law on the natural numbers](lower-tail.md)
- [Lower-tail p-value of a count](lower-tail-pvalue.md)
- [Monotonicity of the lower tail](lower-tail-mono.md)
- [Validity of the lower-tail p-value](is-valid-pvalue-lower-tail-pvalue.md)
- [Survival-function p-values are valid](is-valid-pvalue-survival.md)
- [Validity of a discrete upper-tail p-value](sum-upper-tail-le.md)
- [Validity of the doubled two-sided p-value](is-valid-pvalue-two-sided.md)

- [Confidence sets and test inversion](confidence-sets-and-test-inversion/README.md)

## Genomic control with an estimated inflation factor

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
- [Scores a.s. not all zero, Tⱼ nondegenerate: a covariance is negative](exists-covariance-gc-stat-rv-neg.md)
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

## Type-I error of a calibrated rejection rule

- [Type I error of a p-value rejection rule](type-i-error-le-of-is-valid-pvalue.md)
- [Type I error of a calibrated critical-value rule](type-i-error-le-of-has-law.md)
- [Type I error of a uniform p-value](type-i-error-le-of-has-law-uniform-p-val.md)

## Related topics

- [Genomic control](../../../Biology/statistical-genetics/association-tests/genomic-control/README.md): genomic-control p-values with a known inflation factor λ, exactly calibrated in the common-inflation model, and their calibration in mean in the LD-score model.
