# Restrict Scalars Tensor Iso

Restriction of scalars along a surjective (for instance bijective) map of commutative
rings commutes with tensor products: `M_A ⊗[A] N_A ≅ (M ⊗[B] N)_A`, `m ⊗ n ↦ m ⊗ n`. This is
Mathlib's `TensorProduct.equivOfCompatibleSMul` for the compatible actions of
`TensorProduct.CompatibleSMul.of_algebraMap_surjective`.
