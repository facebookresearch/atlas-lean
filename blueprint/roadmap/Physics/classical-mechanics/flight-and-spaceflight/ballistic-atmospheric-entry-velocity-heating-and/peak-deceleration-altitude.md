# Peak Deceleration Altitude

Candidate peak-deceleration altitude `hstar = H * log (2 * K)`, `K = ballisticK ρ0 H β γ`; it
does not depend on the entry state. For `ρ0, H, β, ve > 0` and `sin γ > 0`, which give `K > 0`,
it is the only stationary point and the strict global maximum of the deceleration
(`deriv_ballisticDeceleration_eq_zero_iff`, `ballisticDeceleration_lt_peak`). For `H > 0` and
`0 < 2 * K ≤ 1` it lies at or below `h = 0`.
