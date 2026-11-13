# Discounted Value

The infinite-horizon discounted value `∑' t, β ^ t * r t` of the reward stream `r`
at discount factor `β`. It is meaningful when the series is summable
(`summable_discounted`); otherwise Lean's `tsum` is `0`.
