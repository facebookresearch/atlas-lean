# First Order decay consumption

The signed integrated balance over `0..t` is `c0 - c(t)`.
It represents nonnegative consumption when `0 ≤ k`, `0 ≤ c0`, and `0 ≤ t`.
Proved from `hasDerivAt_amount` at `R = 0` by the fundamental theorem of
calculus, so it holds for every `t`; for `0 ≤ t` it is also the compartment
mass balance `amount_add_eliminated` at `R = 0` rewritten by `amount_bolus`.
