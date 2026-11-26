# Scalar-extension comparison on balanced pure tensors

Let `k : Type u` and `R : Type v` be commutative rings, `φ : k →+* R`, `M : ModuleCat.{max u v
w} k`, `r∈R`, and `m∈M`. Then `(commutativeIso φ).hom.app M (tensor φ M r m) = r ⊗ₜ[k,φ] m`.
Thus the comparison preserves both entries of each balanced pure tensor.
