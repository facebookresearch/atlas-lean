# Is Counterflow Solution

`(Th, Tc)` solves the counterflow exchanger equations on `[0, L]`, with `x` along the hot flow:
the hot inlet value `Th 0 = Thi` at `x = 0`, the cold inlet value `Tc L = Tci` at `x = L`, and at
every `x ∈ [0, L]` the stream enthalpy flows `Ch * Th` and `Cc * Tc` both have the derivative
`-K * (Th x - Tc x)` within `[0, L]` (one-sided at the ends), that is `Ch * Th' = -K * (Th - Tc)`
and `Cc * Tc' = -K * (Th - Tc)`. The cold equation has the hot equation's sign because `x` runs
against the cold flow. For `0 ≤ L` the predicate depends only on the values of `Th` and `Tc` on
`[0, L]`.
