# Inverse scalar-extension comparison on pure tensors

Let `k : Type u` and `R : Type v` be commutative rings, `φ : k →+* R`, `M : ModuleCat.{max u v
w} k`, `r∈R`, and `m∈M`. Then `(commutativeIso φ).inv.app M (r ⊗ₜ[k,φ] m) = tensor φ M r m`,
the corresponding class in balanced induction.
