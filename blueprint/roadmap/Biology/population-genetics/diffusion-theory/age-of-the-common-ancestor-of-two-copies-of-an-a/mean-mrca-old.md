# Mean Mrca Old

Patterson's `M₂(y)` (Equation 17): in the diffusion reading, the expected MRCA
age of two copies of an old (ancestral) allele now at frequency `y`,
`M₂(y) = 1 - (1 - y) M₁(y) / y`. Meaningful for `y ∈ (0, 1)`; at `y = 1` the Lean
value is `1`, since the `1 - y` factor annihilates the (totalized) `M₁` value.
