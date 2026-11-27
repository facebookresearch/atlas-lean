# For b, ε > 0, exponential absorption into the trapping ellipses

Let `b > 0`, `ε > 0`, `a` and `I` real, `(v, w)` a [solution](is-solution.md),
`C = 5 + I²/2 + a²/(2 b)` the [constant](absorb-const.md) and `κ = min(1, b ε / 2) > 0` the
[decay rate](decay-rate.md). With `E(s) = v(s)² + w(s)²/ε`, for every `t ≥ 0`

`E(t) ≤ e^(-2κt) E(0) + (C / κ)(1 - e^(-2κt))`.

The right-hand side tends to the [trapping radius](trap-radius.md) `C / κ`, so every solution
eventually enters every ellipse `E ≤ R` with `R > C / κ`. The proof applies Grönwall's inequality to
`E' ≤ 2 C - 2 κ E` ([dissipation inequality](energy-flux-le.md)).
