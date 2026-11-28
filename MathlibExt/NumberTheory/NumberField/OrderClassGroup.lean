/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Order
public import MathlibExt.RingTheory.ClassGroup.ExtendedHom

/-!
# The class group of an order and its map to the class group of the maximal order

Let `O` be an order of a number field `K` (`NumberField.IsOrder K O`) and `𝒪_K` the ring of
integers `integralClosure ℤ K`. This file makes `𝒪_K`, as a subalgebra of `K`, a Dedekind domain
with fraction field `K`. The map of class groups `Cl(O) → Cl(𝒪_K)`, `[𝔟] ↦ [𝔟𝒪_K]`, is then
Mathlib's `ClassGroup.map` for the inclusion
`(Subalgebra.inclusion hO.le_integralClosure).toRingHom : O →+* integralClosure ℤ K`, which is
injective (`Subalgebra.inclusion_injective`); `ClassGroup.map_mk` computes it on fractional ideals
over `K`.

Source: K. Conrad, *The conductor ideal of an order*, §5, pp. 13–14 (the group `Cl(O)` and the
map `Cl(O) → Cl(𝒪_K)` given by `[𝔟] ↦ [𝔟𝒪_K]`).
-/

@[expose] public section

variable {K : Type*} [Field K] [NumberField K]

/-- The ring of integers `integralClosure ℤ K`, as a subalgebra, has fraction field `K`. -/
instance NumberField.instIsFractionRingIntegralClosure :
    IsFractionRing (integralClosure ℤ K) K :=
  inferInstanceAs (IsFractionRing (NumberField.RingOfIntegers K) K)

/-- The ring of integers `integralClosure ℤ K`, as a subalgebra, is a Dedekind domain. -/
instance NumberField.instIsDedekindDomainIntegralClosure :
    IsDedekindDomain (integralClosure ℤ K) :=
  inferInstanceAs (IsDedekindDomain (NumberField.RingOfIntegers K))
