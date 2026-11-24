# Two-compartment mass budget

If `(A1, A2)` solves the
two-compartment system in derivative form on (no sign assumptions on the rates are needed) on
`[0, T]` (`A1' = u - (k10 + k12) A1 + k21 A2` and
`A2' = k12 A1 - k21 A2`), then the total amount satisfies
`(A1 + A2)(T) - (A1 + A2)(0) =
∫ s in 0..T, u s - k10 * ∫ s in 0..T, A1 s`: only the input and the
central elimination cross the system boundary.
