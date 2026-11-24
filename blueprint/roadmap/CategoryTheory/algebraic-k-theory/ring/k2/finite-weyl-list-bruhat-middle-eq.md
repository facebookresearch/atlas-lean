# Stable Steinberg Finite Weyl List Monomial

Canonical Bruhat middle of a finite Weyl list product: for pointwise
distinct indices `hij : ∀ k, i k ≠ j k`, the `bruhatMiddle` of the head-left
`List.ofFn`/`List.prod` ordered product of `weylSLUnit (i k) (j k) (hij k)`
`(u k)` is the ordered product of the accepted `weylMonomialSLUnit`
realizations in the same `List.ofFn` order. `[Field F]` is required by the
`bruhatMiddle_monomialSLHom` retraction; the pointwise step is
`[CommRing]`-general. The empty list gives `bruhatMiddle 1 = 1`; low ranks
need no special case since the statement is uniform in `m n`. Orientation is
head-left throughout. Nonclaims: no StableE evaluation, kernel hypothesis,
permutation-triviality, torus landing, subgroup containment, kernel generation,
or Matsumoto claim.
