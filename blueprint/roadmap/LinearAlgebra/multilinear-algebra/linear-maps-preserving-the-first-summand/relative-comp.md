# Relative maps respect composition

Let `R` be a commutative ring and `M,N,M',N'` be `R`-modules. A `FirstSummandMap f` consists
of an `R`-linear `f.map : M×N → M'×N'` and `f.first : M → M'` with `f.map ∘ inl = inl' ∘
f.first`. For another first-summand-preserving map `g`, `(f.comp g).relative = g.relative ∘
f.relative`.
