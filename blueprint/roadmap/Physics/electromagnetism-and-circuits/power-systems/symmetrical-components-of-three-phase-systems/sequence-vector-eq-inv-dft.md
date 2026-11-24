# Sequence components are the inverse DFT of the phases

For all complex `V_a`, `V_b`, `V_c`, the [sequence array](sequence-vector.md) `(V₀, V₁, V₂)` is the
inverse discrete Fourier transform of the phase quantities `(V_a, V_b, V_c)`, viewed as a function
on the integers modulo 3 ([phase array](phase-vector.md)): `V_s = (1/3) Σ_j e^(2πi js/3) f(j)` with
`f` the phase array.

Equivalently, `V_s` is the normalized DFT of the phase array read at the negated frequency `-s`:
with the DFT `F(k) = Σ_j e^(-2πi jk/3) f(j)`, which has a negative exponent, `V_s = F(-s) / 3`, so
the sequence components are the normalized DFT at frequencies `0`, `2`, `1`.
