# Is Parallel Flow Solution

`(Th, Tc)` solves the parallel-flow exchanger equations on `[0, L]` with both inlets at
`x = 0`: `Th 0 = Thi`, `Tc 0 = Tci`, and at every `x ∈ [0, L]` the stream enthalpy flows
`Ch * Th` and `Cc * Tc` have the derivatives `-K * (Th x - Tc x)` and `K * (Th x - Tc x)` within
`[0, L]` (one-sided at the ends), that is `Ch * Th' = -K * (Th - Tc)` and
`Cc * Tc' = K * (Th - Tc)`. For `0 ≤ L` the predicate depends only on the values of `Th` and `Tc`
on `[0, L]`.
