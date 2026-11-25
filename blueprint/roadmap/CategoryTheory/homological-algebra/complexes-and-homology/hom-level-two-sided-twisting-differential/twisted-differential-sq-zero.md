# Twisted Differential sq zero

Square-zero of the two-sided twisting differential from the Maurer-Cartan
equation.

For `f : Cochain C A n` and `τ : Cochain C A 1` with `IsMaurerCartan τ`,
two applications of `twistedDifferential` give degree `(n + 1) + 1`.
Expanding with `HomComplex.δ_δ`, `conv_leibniz` on both legs,
additive/scalar convolution laws, and `conv_assoc`, the `δf ⋆ τ` and
`τ ⋆ δf` pairs cancel by `(n + 1).negOnePow = -n.negOnePow`, the mixed
`(τ ⋆ f) ⋆ τ` terms cancel by associativity, `n.negOnePow ^ 2 = 1` leaves
the two curvatures `(δτ + τ ⋆ τ) ⋆ f` and `f ⋆ (δτ + τ ⋆ τ)`, and the
Maurer-Cartan equation closes both.
