# For 0 ≤ c ≤ e with e > 0, propagule rain ensures persistence

For `0 ≤ c ≤ e` with `e > 0`, and every `m > 0`, two statements hold. Without immigration,
extinction `p = 0` is [globally stable](is-globally-stable-3.md) on `[0, 1]` for the Levins model:
it is Lyapunov stable and attracts every Levins solution starting in `[0, 1]`. With immigration rate
`m`, the [immigration equilibrium](immigration-eq.md) is positive, `p̂ > 0`, and
[globally stable](is-globally-stable.md) on `[0, ∞)`: it is Lyapunov stable for the solutions with
`p(0) ≥ 0` and attracts every [forward solution of the equation with immigration](is-solution.md)
with `p(0) ≥ 0`.

Immigration only colonizes empty patches and leaves the extinction rate `e` unchanged, so this is
not the rescue effect.
