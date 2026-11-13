# Sample mean family MSE under iid

For square-integrable identically distributed
`X i` with `n > 0`, the family MSE of `X̄` about the constant mean family over `Unit`
equals `Var (X 0) / n`. Adds independence for the variance calculation
(via `variance_sample_mean_of_iid`); the squared-error integrability is constructed
internally from `hMemLp`, identical distribution, and finite summation.
