# Scalar-extension comparison on the unit class

Let `k : Type u` and `R : Type v` be commutative rings, `φ : k →+* R`, `M : ModuleCat.{max u v
w} k`, and `m∈M`. The component of `commutativeIso φ` sends `tensor φ M 1 m` to `(1 : R)
⊗ₜ[k,φ] m`, where the `k`-action on `R` is through `φ`.
