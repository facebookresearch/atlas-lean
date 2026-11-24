# The production–decay inventory solves its rate equation

Production–decay (exposure-age) model: for a decay constant `λ > 0` and every real `P`, `N0`
and `t`, the function `N(t) = N0 * exp (-λ * t) + (P / λ) * (1 - exp (-λ * t))` has derivative
`P - λ * N(t)` at `t`, so it solves `N' = P - λ * N`. It describes a nuclide inventory under
constant production only on the physical domain `P ≥ 0`, `N0 ≥ 0`, `t ≥ 0`.
