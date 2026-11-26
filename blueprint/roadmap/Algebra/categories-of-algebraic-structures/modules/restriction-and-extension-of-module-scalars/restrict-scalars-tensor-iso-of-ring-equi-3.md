# Inverse tensor comparison on pure tensors

Let `R,S : Type s` be commutative rings, `e : R ≃+* S`, `M,N : ModuleCat.{s} S`, `m∈M`, and
`n∈N`. The inverse map of `restrictScalarsTensorIsoOfRingEquiv e M N` sends `m ⊗ₜ[S] n` to `m
⊗ₜ[R] n` in `F(M) ⊗_R F(N)`, where `F` restricts scalars along `e`.
