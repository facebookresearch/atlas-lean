# Speiser's lemma

**Speiser's lemma** (Galois descent for vector spaces): let `Γ` be a finite Galois group of
the field extension `L/K` (`IsGaloisGroup Γ K L`; for instance `Γ = Gal(L/K)` for a finite
Galois extension `L/K`), and let `Γ` act semilinearly and `K`-linearly on an `L`-vector space `W`
(`g • (a • w) = (g • a) • (g • w)`). Then the natural `L`-linear map
`L ⊗_K W^Γ → W`, `a ⊗ w ↦ a • w`, is bijective, where
`W^Γ = (Representation.ofDistribMulAction K Γ W).invariants`.
