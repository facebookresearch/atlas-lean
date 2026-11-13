# The property of Storey's estimator that the FDR proof uses

Let `π̂₀⁽ⁱ⁾` be Storey's
estimator computed with `p i` replaced by `0` (equivalently, from the other p-values). If each
true-null p-value is valid and independent of the other p-values, then
`∑_{i ∈ H0} E[1 / π̂₀⁽ⁱ⁾] ≤ m`, for `0 ≤ lam < 1`. Combined with the leave-one-out property this
gives
`E[FDP] ≤ ∑_{i ∈ H0} (q / m) E[1 / π̂₀⁽ⁱ⁾] ≤ q`. This is a bound on the *inverse* of the
leave-one-out estimator; conservativeness in expectation, `E[π̂₀] ≥ |H0| / m`
(`TwoGroupsTesting.le_integral_storeyPi0`), does not imply it (Jensen goes the wrong way).
