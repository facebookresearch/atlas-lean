# For a ≠ 0, the calibrated estimator has expectation x + e / a

Let `μ` be a probability measure and let the error `ε` be a random variable that is integrable with
respect to `μ`, with expectation `e = ∫ ε dμ`. For real `a ≠ 0`, `b` and `x`, the calibrated
estimator of the reading `y = a x + b + ε` has expectation `∫ (a x + b + ε - b) / a dμ = x + e / a`.
In particular it is unbiased, with expectation `x`, when `e = 0`.

The slope `a` is known; a fitted slope makes the estimator a nonlinear function of the data and is
not covered.
