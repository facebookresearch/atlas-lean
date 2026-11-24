# The positive sequence is not the normalized DFT at frequency 1

For `(V_a, V_b, V_c) = (0, 1, 0)`, the [positive-sequence component](positive-sequence.md) `α / 3`
differs from the normalized DFT of the phase array at frequency `1`, which is `α² / 3`. So reading
the sequence components at frequencies `0`, `1`, `2` would be wrong; they sit at `0`, `2`, `1`
([negated frequencies](sequence-vector-eq-normalized-dft-neg.md)). Here the DFT on the integers
modulo 3 is `F(k) = Σ_j e^(-2πi jk/3) f(j)`, with a negative exponent, and the normalized DFT is
`F(k) / 3`.
