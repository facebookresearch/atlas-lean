# Sequence components are the inverse DFT of the phases

For all complex `V_a`, `V_b`, `V_c`, the [sequence array](sequence-vector.md) `(V₀, V₁, V₂)` is the
inverse discrete Fourier transform of the phase quantities `(V_a, V_b, V_c)`, viewed as a function
on the integers modulo 3 ([phase array](phase-vector.md)): `V_s = (1/3) Σ_j e^(2πi js/3) f(j)` with
`f` the phase array.
