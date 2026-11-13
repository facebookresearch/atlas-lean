# James–Stein estimator

The James–Stein estimator `δ(x) = (1 - (p - 2) / ‖x‖²) x` of the mean of `N(θ, I_p)`. At
`x = 0` the factor is `1` by Lean's `a / 0 = 0` convention, so `δ(0) = 0`.
