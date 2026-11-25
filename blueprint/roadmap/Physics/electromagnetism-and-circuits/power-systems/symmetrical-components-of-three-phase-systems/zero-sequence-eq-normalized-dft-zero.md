# The zero sequence is the normalized DFT at frequency 0

For all complex `V_a`, `V_b`, `V_c`, the [zero-sequence component](zero-sequence.md)
`V₀ = (V_a + V_b + V_c) / 3` is the normalized DFT of the phase quantities `(V_a, V_b, V_c)`, viewed
as a function on the integers modulo 3 ([phase array](phase-vector.md)) at frequency `0`. Here the
DFT on the integers modulo 3 is `F(k) = Σ_j e^(-2πi jk/3) f(j)`, with a negative exponent, and the
normalized DFT is `F(k) / 3`.
