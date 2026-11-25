# Strictly monotone approach from below

Let `Vmax > 0` and `Km > 0`, let `R` be a real infusion rate, and let `C` be differentiable at every
time `t ≥ 0` with `C'(t) = R - Vmax * C(t) / (Km + C(t))` (saturable elimination under constant
infusion). Let `c ≥ 0` be an equilibrium: `Vmax * c / (Km + c) = R`.

If `0 ≤ C(0) < c`, then `C` is strictly increasing on `[0, ∞)`.
