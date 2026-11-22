# Affine recurrence convergence

An affine recursion `b[t+1] = a * b[t] + d`
with `|a| < 1` converges to the fixed point `d / (1 - a)`. This is a
specialization of geometric decay (`tendsto_pow_atTop_nhds_zero_of_abs_lt_one`).
