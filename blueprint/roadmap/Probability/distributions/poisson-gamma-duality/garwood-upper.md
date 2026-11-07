# Garwood's exact upper confidence bound

**Garwood's exact upper confidence bound** for a Poisson mean after observing `k`, at
level `α`: `u_α(k) = sup {x ≥ 0 | α ≤ F_k(x)}`. For `0 < α < 1` it is the root of
`F_k(u) = α` (`poissonCDF_garwoodUpper`).
