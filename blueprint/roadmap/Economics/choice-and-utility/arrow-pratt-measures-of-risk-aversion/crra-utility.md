# CRRA (isoelastic) utility

For a real parameter `γ`, the constant relative risk aversion (CRRA, isoelastic) utility of wealth
`x` is `u(x) = x^(1-γ) / (1-γ)` for `γ ≠ 1` and `u(x) = log x` for `γ = 1`. It is defined for every
real `x`: at `x = 0` the conventions `log 0 = 0` and `0^y = 0` for `y ≠ 0` make it `0`, and for
`x < 0` it uses `log x = log |x|` and `x^y = |x|^y cos(π y)`; the intended domain is `x > 0`.
