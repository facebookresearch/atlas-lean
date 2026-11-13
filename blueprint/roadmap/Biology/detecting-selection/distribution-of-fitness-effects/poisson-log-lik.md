# Poisson log-likelihood of counts

The Poisson log-likelihood `∑ (k_i log E_i - E_i - log k_i!)` of counts `k_i` with means
`E_i`. Meaningful for `E_i > 0`; at `E_i = 0` Lean's `log 0 = 0` gives a junk value.
