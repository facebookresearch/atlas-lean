# Totalized form, no hypotheses

`V̂(t)` equals the unfiltered sum over all `tⱼ ≤ t` *as a
Lean expression*: at an excluded time (`dⱼ = Yⱼ`) the textbook summand is undefined, and the Lean
term `dⱼ / (Yⱼ · 0)` is `0` only by the convention `x / 0 = 0`. This is an identity of totalized
expressions, not agreement with the textbook formula; for that see
`greenwoodVariance_eq_textbook`.
