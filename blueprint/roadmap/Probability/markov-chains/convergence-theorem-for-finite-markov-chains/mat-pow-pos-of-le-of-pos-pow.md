# Later powers of a positive stochastic matrix power stay positive

If some power `w` of a stochastic matrix is all-positive, then every later
power `m ≥ w` is all-positive: write `m = (m - w) + w`, use `matPow_add`, and
note that row `i` of `matPow (m - w)` sums to `1`, so some entry of that row is
positive, and that entry times the positive `matPow w` entry gives a positive
summand.
