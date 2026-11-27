# For 0 ≤ e < c, extinction is not Lyapunov stable

**Extinction is unstable above the threshold.** If `0 ≤ e < c`, the extinction equilibrium `p = 0`
is not [Lyapunov stable](is-lyapunov-stable-2.md) for the [solutions](is-solution-2.md) of the
Levins equation `p' = c p (1 - p) - e p` starting in `[0, 1]`: there is `ε > 0` such that for
every `δ > 0` some solution with `p(0) ∈ [0, 1]` and `p(0) < δ` satisfies `|p(t)| ≥ ε` at some time
`t ≥ 0`. Indeed solutions with `p(0) > 0` [tend to](tendsto-persistence-eq.md)
`p* = 1 - e / c > 0`.
