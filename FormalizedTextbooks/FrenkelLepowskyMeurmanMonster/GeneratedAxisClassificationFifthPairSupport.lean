/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthPairData

/-! All 552 actual middle pair-short coefficients of the fifth transition vanish. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators

/-- The inverse actual physical pair line never belongs to the original coordinate octad plane. -/
theorem generatedFifth_inverse_pair_not_supported (s : Fin 2) (p : Fin 276) :
    ¬ (∀ i : Fin 24, Nat.testBit 0xcccc00 i.val = false →
      (generatedFifthLocalFiber⁻¹).val.2.val (griessShortVector (Sum.inl (s, p))) i = 0) := by
  intro h
  have hlt : (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
    (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  obtain ⟨i, hi, hn⟩ := generatedFifth_pair_outside_certificate s _ _ hlt
  have hz := (generatedFifth_inverse_short_zero (Sum.inl (s, p)) i).mp (h i hi)
  apply hn
  simpa [Matrix.mulVec, dotProduct, griessShortIntegral, mul_add, mul_ite, ite_mul,
    Finset.sum_add_distrib] using hz

/-- Every genuine middle pair-short coefficient is zero, with no central-phase assumption. -/
theorem generatedFifth_middle_pair_zero (s : Fin 2) (p : Fin 276) :
    localShortOperator generatedFifthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 (Sum.inl (s, p)) = 0 := by
  by_contra h
  have hh := (generatedFourth_transported_short_support generatedFifthLocalFiber
    generatedFourthOctad 0 0 (Sum.inl (s, p))).mp h
  apply generatedFifth_inverse_pair_not_supported s p
  simpa only [generatedFourthOctad_mask] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
