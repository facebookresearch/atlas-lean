# The relative component is the second projection of the image

Let `R` be a commutative ring and `M,N,M',N'` be `R`-modules. A `FirstSummandMap f` consists
of an `R`-linear `f.map : M×N → M'×N'` and `f.first : M → M'` with `f.map ∘ inl = inl' ∘
f.first`. The maps satisfy `snd' ∘ f.map ∘ inr = f.relative : N →ₗ[R] N'`.
