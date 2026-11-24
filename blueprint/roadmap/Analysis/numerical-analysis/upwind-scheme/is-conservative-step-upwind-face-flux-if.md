# The conservative upwind step is the classical upwind update

For a natural number `n`, real numbers `A > 0`, `Δx > 0`, `Δt` and `v ≥ 0`, and cell values `c`,
`c'` indexed by `ℤ/nℤ`, the [conservative step](is-conservative-step.md) from `c` to `c'` with the
[upwind face flux](upwind-face-flux.md) of `c` holds if and only if
`c'(i) = (1 - ν) c(i) + ν c(i - 1)` for every `i`, where `ν = v Δt / Δx` is the Courant number.
