# Ipw Contrast

The **inverse probability weighting contrast** of an observed outcome `Y`,
`E[1_T Y / e(X) - 1_{Tᶜ} Y / (1 - e(X))]`, where `e = propensity μ T X` is the propensity score.
It depends on the law of the observed data `(T, X, Y)` only. `IsIPWNull` pairs its vanishing
with integrability, so an undefined expectation is not counted as a zero observed-data null.

## Sources

- the left-hand side of `integral_ipw_ate` (Horvitz & Thompson 1952; Rosenbaum 1987).
