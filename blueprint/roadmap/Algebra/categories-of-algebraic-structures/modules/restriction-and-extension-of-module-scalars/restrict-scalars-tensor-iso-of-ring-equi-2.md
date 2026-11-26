# Forward tensor comparison on pure tensors

Let `R,S : Type s` be commutative rings, `e : R ≃+* S`, `M,N : ModuleCat.{s} S`, `m∈M`, and
`n∈N`. The forward map of `restrictScalarsTensorIsoOfRingEquiv e M N` sends `m ⊗ₜ[R] n` in the
restricted modules to `m ⊗ₜ[S] n` in the restricted `S`-tensor product.
