# Composition of first-summand-preserving maps

Let `R` be a commutative ring and `M,N,M',N'` be `R`-modules. A `FirstSummandMap f` consists
of an `R`-linear `f.map : M×N → M'×N'` and `f.first : M → M'` with `f.map ∘ inl = inl' ∘
f.first`. For another such map `g : M'×N' → M''×N''`, the composite has total map `g.map ∘
f.map` and first map `g.first ∘ f.first`, with the composed first-inclusion square.
