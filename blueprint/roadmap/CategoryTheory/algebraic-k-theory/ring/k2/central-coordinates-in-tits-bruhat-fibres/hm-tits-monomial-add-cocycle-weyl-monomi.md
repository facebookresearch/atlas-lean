# Hm Tits Monomial Add Cocycle weyl Monomial Base Unit 01 one torus Monomial Base Unit 01

Simple Weyl / diagonal-torus cocycle in `Fin 3` at the simple root `(0,1)`.

This is the **central correction** primitive: the additive monomial cocycle
`hmTitsMonomialAddCocycle` evaluated at the unit-one Weyl element
`weylMonomialBaseUnit 0 1 _ (1 : Fˣ)` and the torus element
`torusMonomialBaseUnit 0 1 _ u` is

` - {u,u}` in `MilnorK F 2`.

It does **not** vanish in general; we make no claim that the associated
central gauge `leftWeylCentralGauge_torusSLUnit` is trivial – that statement
is false in general and is not proved here.

Derivation (sign verified from pinned definitions in
`BruhatSimpleRoot.lean`, `PermutationBilinearSchurTitsCocycle.lean`,
`PermutationBilinearTitsAction.lean`, `PermutationSchurCocycle.lean`,
`MatsumotoPermutationAction.lean`):

- `torusWeightUnit (0) (1) _ u = balancedPairTuple (0) (1) u` by `rfl`
  (both `fun k => if k=0 then u else if k=1 then u⁻¹ else 1`);
  thus `torusMonomialBaseUnit = ⟨balancedPairTuple, 1⟩`.
- `weylWeightUnit (0) (1) _ 1 = singleSupportTuple 1 (-1)` by the private
  helper above, verified from the definitions
  `weylWeightUnit i j _ u = if k=i then u else if k=j then -u⁻¹ else 1`.
  Hence `weylMonomialBaseUnit 0 1 _ 1 = ⟨singleSupportTuple 1 (-1), swap 0 1⟩`.
- `hmTitsMonomialAddCocycle = schurTitsMonomialAddCocycle b (-1) schurElement …`,
  `schurTits = titsMonomialAddCocycle + schurCocycleWith`.
  The Schur part vanishes by `schurCocycleWith_one_right` since the torus
  permutation is `1`.
- `titsMonomialAddCocycle b eps P Q = titsAlphaAdd b eps P.left (permute P.right Q.left)
   + titsQAdd b eps P.right Q.left`.
  `permute (swap 0 1) (balanced 0 1 u)` equals `balanced 1 0 u`
  by `permute_balancedPairTuple`, then equals `balanced 0 1 u⁻¹`
  by `balancedPairTuple_swap` (with `0≠1` in `Fin 3`).
- `titsAlphaAdd` of `singleSupportTuple 1 (-1)` against `balanced 0 1 u⁻¹`
  is `b.eval (singleSupportTuple 1 (-1) 0) u⁻¹` by
  `titsAlphaAdd_balancedPair_right` using `IsAdjacentPair 0 1` (`rfl`:
  `1.val = 0.val+1` in `Fin 3`). The first component is `1`, so the value is
  `0` by `milnorK2Bicharacter_eval` and `k2Symbol_one_left`.
- `titsQAdd (swap 0 1) (balanced 0 1 u) = - b.eval u u`
  by `titsQAdd_swap_balancedPair` with `0≠1` in `Fin 3`,
  and `b.eval u u = k2Symbol F u u` by `milnorK2Bicharacter_eval`.

Thus the cocycle equals `- {u,u}`. We explicitly do **not** claim it vanishes
and we do not deduce any triviality of Weyl central gauges.
