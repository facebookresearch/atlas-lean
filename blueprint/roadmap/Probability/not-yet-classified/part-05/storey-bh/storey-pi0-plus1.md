# Storey's estimator of the proportion of true nulls

**Storey's estimator of the proportion of true nulls** with tuning parameter `lam`, in the
finite-sample form used by Storey, Taylor and Siegmund (2004, Theorem 3):
`π̂₀(lam) = (#{j : p j > lam} + 1) / ((1 - lam) m)`. The `+ 1` keeps `π̂₀ > 0` when `0 < m`
and `lam < 1`, and is used in the FDR proof (`sum_integral_inv_storeyPi0Plus1_update_le`).
