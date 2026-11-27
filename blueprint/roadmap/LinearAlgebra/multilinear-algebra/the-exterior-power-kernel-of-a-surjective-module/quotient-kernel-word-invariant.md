# The quotient word depends only on slot images

Let `R` be a commutative ring, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. Let `n : ℕ` and `v,w
: Fin n → M` satisfy `f(v i)=f(w i)` for every `i`. Then `quotientKernelWord f n v =
quotientKernelWord f n w` in `Λ^n_R M / kernelSlotWords f n`.
