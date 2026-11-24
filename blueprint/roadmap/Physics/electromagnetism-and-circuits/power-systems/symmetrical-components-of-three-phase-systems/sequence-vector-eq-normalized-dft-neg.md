# Sequence components are the normalized DFT at negated frequencies

For all complex `V_a`, `V_b`, `V_c`, the [sequence array](sequence-vector.md) `(V₀, V₁, V₂)` at
index `s` is the normalized DFT of the phase quantities `(V_a, V_b, V_c)`, viewed as a function on
the integers modulo 3 ([phase array](phase-vector.md)) at frequency `-s`: the sequence components
are the normalized DFT read at frequencies `0`, `2`, `1`. Here the DFT on the integers modulo 3 is
`F(k) = Σ_j e^(-2πi jk/3) f(j)`, with a negative exponent, and the normalized DFT is `F(k) / 3`.
