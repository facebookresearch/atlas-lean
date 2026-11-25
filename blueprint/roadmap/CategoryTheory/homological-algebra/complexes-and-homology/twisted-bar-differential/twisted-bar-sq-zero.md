# Twisted Bar sq zero

Square-zero of the right-twisted bar differential from the Maurer–Cartan
equation, with curvature factoring on the right as `f ⋆ (δτ + τ ⋆ τ)`.

For `f : Cochain C A n` and `τ : Cochain C A 1` with `IsMaurerCartan τ`,
two applications of `twistedBarDifferential` give the exact degree
`(n + 1) + 1` forced by the definition. Expanding with `HomComplex.δ_δ`,
`conv_leibniz`, additive/scalar convolution laws, and `conv_assoc`, the
`(δf ⋆ τ)` terms cancel by `(n + 1).negOnePow = -n.negOnePow`, the
`n.negOnePow ^ 2 = 1` normalization leaves `-f ⋆ (δτ) - f ⋆ (τ ⋆ τ)`,
and the Maurer–Cartan equation closes the curvature factor.
