# The negative sequence is the normalized DFT at frequency 1

For all complex `V_a`, `V_b`, `V_c`, the [negative-sequence component](negative-sequence.md)
`V₂ = (V_a + α² V_b + α V_c) / 3` is the normalized DFT of the phase quantities `(V_a, V_b, V_c)`,
viewed as a function on the integers modulo 3 ([phase array](phase-vector.md)) at frequency `1`.
Here the DFT on the integers modulo 3 is `F(k) = Σ_j e^(-2πi jk/3) f(j)`, with a negative exponent,
and the normalized DFT is `F(k) / 3`.
