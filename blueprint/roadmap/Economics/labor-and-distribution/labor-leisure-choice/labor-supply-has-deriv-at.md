# Labor-supply Slutsky decomposition

Let a household have time endowment `T` and nonlabor income `N`, and let
Marshallian leisure demand `(w, M) ↦ ℓ(w, M)`, at wage `w` and full income `M`, have
derivative `D` (a linear map) at `(w, w * T + N)`, so that `D(1, 0)` is the own-wage
effect at fixed full income and `D(0, 1)` the full-income effect. Write
`ℓ = ℓ(w, w * T + N)` for leisure and `L = T - ℓ` for labor supply, and let `s`, the
compensated (Hicksian) wage derivative of leisure, satisfy the Slutsky identity
`s = D(1, 0) + D(0, 1) * ℓ`, which is assumed (it is the conclusion of the consumer
Slutsky equation for the good leisure at price `w`).
Then the uncompensated wage effect on labor supply is the compensated effect
`-s` minus the income effect: `w ↦ T - ℓ(w, w * T + N)` has derivative
`-s - L * D(0, 1)` at `w`.

With leisure a normal good (`0 < D(0, 1)`), positive labor supply and a
nonpositive compensated own-wage effect on leisure (`s ≤ 0`), the income effect
`-L * D(0, 1)` works against the substitution effect `-s`, which is the source of
a backward-bending labor-supply curve. Without `s ≤ 0` both terms can have the
same sign.
