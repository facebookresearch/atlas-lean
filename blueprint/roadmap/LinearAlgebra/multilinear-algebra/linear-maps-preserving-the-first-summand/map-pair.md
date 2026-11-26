# The first-summand-preserving map is triangular

Let `R` be a commutative ring and `M,N,M',N'` be `R`-modules. A `FirstSummandMap f` consists
of an `R`-linear `f.map : M×N → M'×N'` and `f.first : M → M'` with `f.map ∘ inl = inl' ∘
f.first`. For `x : M` and `y : N`, `f.map(x,y)=(f.first x + f.offDiagonal y, f.relative y)`.
