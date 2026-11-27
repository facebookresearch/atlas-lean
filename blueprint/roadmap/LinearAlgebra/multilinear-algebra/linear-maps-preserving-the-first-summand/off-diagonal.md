# The off-diagonal component of the linear map

Let `R` be a commutative ring and `M,N,M',N'` be `R`-modules. A `FirstSummandMap f` consists
of an `R`-linear `f.map : M×N → M'×N'` and `f.first : M → M'` with `f.map ∘ inl = inl' ∘
f.first`. The map `f.offDiagonal : N →ₗ[R] M'` is `fst' ∘ f.map ∘ inr`.
