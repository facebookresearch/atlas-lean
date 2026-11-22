# Gibbs' inequality

For a probability distribution `p` (`0 ≤ p i`, `∑ i, p i = 1`) and a
probability distribution `q` with `0 < q i`, the relative entropy `∑ i, p i * log (p i / q i)` is
nonnegative. No support hypothesis on `p` is needed: a state with `p i = 0` contributes `0`. This
is the case `∑ i, p i = ∑ i, q i = 1` of the log-sum inequality
`Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div`.
