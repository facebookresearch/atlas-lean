# Amount just after the n-th dose of a periodic schedule

For a dose `D`, an elimination rate `k`, a dosing interval `τ` (real numbers) and a natural number
`n`, the amount just after dose `n` of the fixed-spacing schedule is
`P(n) = ∑_{i=0}^{n} D * exp (-k * (n * τ - i * τ))`: the sum of the first `n + 1` doses, given at
the times `i * τ`, each decayed from its event time to `n * τ`. For `τ > 0` it is the value at the
event time of the [periodic trajectory](periodic-amount-decay.md).
