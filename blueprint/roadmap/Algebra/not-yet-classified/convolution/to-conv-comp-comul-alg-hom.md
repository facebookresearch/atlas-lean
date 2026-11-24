# Post-composition splits the comultiplication point into its two inclusions

For any
algebra map `φ` out of the tensor square, the point `φ ∘ Δ` is the convolution product of `φ`
restricted along the two inclusions.

The convolution monoid here is the one on points of `H` with values in the *commutative* algebra
`A`, so `H` itself need only be a semiring: the tensor square `H ⊗[R] H` is used solely as the
source of `φ`, never as a convolution target. That is why this is proved from the linear-map
identity `MathlibExt.Coalgebra.comul_eq_convMul_includeLeft_includeRight` rather than from
`MathlibExt.Bialgebra.comulPoint_eq_include_mul`, which needs `H ⊗[R] H` to be commutative.
