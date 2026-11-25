# Inclusion N

The inclusion of the normalized chains `N X` of the pseudoabelian Dold–Kan correspondence
into the alternating face map complex of `X`, as the direct summand cut out by `PInfty`.

By definition `N = N₁ ⋙ (toKaroubiEquivalence _).inverse`, so `N.obj X` is the object of chain
complexes corresponding to the formal direct summand `N₁.obj X` of the Karoubi envelope, whose
underlying complex is the alternating face map complex of `X` with idempotent `PInfty`
(`AlgebraicTopology.DoldKan.N₁_obj_p`); the counit of `toKaroubiEquivalence` identifies the two.
