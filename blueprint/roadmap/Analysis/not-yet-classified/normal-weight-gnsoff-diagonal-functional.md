# Normal functional of two finite square GNS vectors

Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an
extended positive weight: additive, homogeneous for finite nonnegative real scalars, and
zero at zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into
the weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume
`φ` preserves least upper bounds of nonempty norm-bounded directed positive sets. for `x,y
∈ n_φ`, `normalWeightGNSOffDiagonalFunctional M φ x y` returns `ρ ∈ M_*` whose underlying
bounded functional is `representationCoefficient π (Λ x) (Λ y)`, with value
`ρ(a)=⟨Λ(y),π(a)Λ(x)⟩`.
