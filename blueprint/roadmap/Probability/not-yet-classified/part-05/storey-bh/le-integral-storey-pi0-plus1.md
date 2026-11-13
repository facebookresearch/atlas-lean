# The `+ 1` estimator is conservative in expectation

If every true-null p-value is valid
and `lam ∈ [0, 1)`, then `E[storeyPi0Plus1 lam] ≥ |H0| / m`. Derived from main's
`TwoGroupsTesting.le_integral_storeyPi0` and the pointwise bound `storeyPi0_le_storeyPi0Plus1`;
no independence is needed. Not used by the FDR theorem, and not sufficient for it.
