# Renewal equation for exponential growth

For `c ≠ 0`, the exponential
`b(t) = c e^{r t}` solves `b(t) = R ∫ b(t - a) g(da)` for every `t` iff `R M_g(-r) = 1`.
This is meaningful when `a ↦ e^{-r a}` is `g`-integrable; otherwise Lean's integral and
`M_g(-r)` are both `0` and both sides of the equivalence are false.
