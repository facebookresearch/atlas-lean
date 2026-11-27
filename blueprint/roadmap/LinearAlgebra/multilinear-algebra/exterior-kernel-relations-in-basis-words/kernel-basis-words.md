# Kernel vectors followed by basis tails

Let `R` be a commutative ring, `M` an `R`-module with basis `b : Basis I R M`, and `n : ℕ`.
For an `R`-module `N` and `f : M →ₗ[R] N`, `kernelBasisWords f b n` is the span in `Λ^(n+1)_R
M` of words `ιMulti_R(Fin.cons y (b ∘ x))` with `y : M`, `f y=0`, and `x : Fin n → I`.
