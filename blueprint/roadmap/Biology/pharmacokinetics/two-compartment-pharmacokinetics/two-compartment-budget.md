# Two-compartment mass budget

Let `T ≥ 0` and let `k10`, `k12` and `k21` be real rates (no signs are needed). Let `u` be an input
integrable on `[0, T]`, and let the amounts `A1` and `A2` have the derivatives
`A1'(s) = u(s) - (k10 + k12) * A1(s) + k21 * A2(s)` and `A2'(s) = k12 * A1(s) - k21 * A2(s)` at
every `s` in `[0, T]`. Then the total amount satisfies
`(A1(T) + A2(T)) - (A1(0) + A2(0)) = ∫₀ᵀ (u(s) - k10 * A1(s)) ds`: only the input and the central
elimination cross the system boundary.
