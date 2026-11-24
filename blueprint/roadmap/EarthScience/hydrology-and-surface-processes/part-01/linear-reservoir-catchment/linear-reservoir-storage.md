# Storage of a linear reservoir with constant inflow

For a constant inflow `I`, a recession coefficient `k`, an initial storage `S0` and a time `t`
(real numbers), the storage of the linear reservoir is
`S(t) = I / k + (S0 - I / k) * exp (-k * t)`. It is defined for every real `k`, with the
convention `x / 0 = 0`: for `k = 0` the storage is constantly `S0`. The physical decay regime is
`k > 0`, where `I / k` is the steady storage.
