# Steady-state concentration under constant infusion

For real numbers `Vmax`, `Km` and `R`, the steady-state concentration under constant infusion at the
rate `R` is `C∞ = R * Km / (Vmax - R)`. It is defined for all real inputs; with the convention
`x / 0 = 0` it is `0` at `R = Vmax`. For `Vmax > 0`, `Km > 0` and `0 ≤ R < Vmax` it is the
[unique](eq-steady-conc-of-mm-rate-eq.md) [nonnegative](steady-conc-nonneg.md) concentration at
which elimination [balances the infusion](mm-rate-steady-conc.md), `Vmax * C∞ / (Km + C∞) = R`.
