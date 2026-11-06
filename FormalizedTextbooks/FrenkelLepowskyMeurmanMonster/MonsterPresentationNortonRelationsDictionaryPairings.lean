/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite source-dictionary pairings for the exact sparse Norton half-word certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortDictionaryPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityInvariance

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Pairing with an A, B, or C source unit extracts twice its source coordinate. -/
theorem monsterNortonForm_ABC_right (x : GriessSpace) (s : Fin 3) (p : Fin 276) :
    griessForm x (trialityABCBasis s p) = 2 * (trialityBlocksEquiv x).2.1 s p := by
  rw [griessForm_eq_trialityBlockForm, trialityABCBasis_blocks]
  simp [trialityBlockForm, Pi.single_apply, ite_apply, mul_ite, Finset.sum_ite_eq']

/-- The source A, B, and C units are orthogonal, with their genuine squared norm two. -/
theorem monsterNortonForm_ABC_ABC (s t : Fin 3) (p q : Fin 276) :
    griessForm (trialityABCBasis s p) (trialityABCBasis t q) =
      if s = t ∧ p = q then 2 else 0 := by
  rw [monsterNortonForm_ABC_right, trialityABCBasis_blocks]
  by_cases hs : s = t <;> by_cases hp : p = q <;> simp [hs, hp, Ne.symm]

/-- A whole actual octad packet has no A, B, or C source coordinate. -/
theorem monsterNortonForm_octad_ABC (d : Fin 759) (v : Fin 64 → ℝ)
    (s : Fin 3) (p : Fin 276) :
    griessForm (monsterNortonOctadShortVector d v) (trialityABCBasis s p) = 0 := by
  rw [monsterNortonForm_ABC_right, monsterNortonOctadShortVector_blocks]
  simp only [Pi.zero_apply, mul_zero]

/-- Pairing a whole actual octad packet with a unit reads exactly its indicated coordinate. -/
theorem monsterNortonForm_octad_unit (d f : Fin 759) (v : Fin 64 → ℝ) (e : Fin 64) :
    griessForm (monsterNortonOctadShortVector d v)
      (monsterNortonPureShort (Sum.inr (Sum.inl (f, e)))) =
        if d = f then v e else 0 := by
  rw [monsterNortonForm_pureShort_right]
  unfold monsterNortonOctadShortVector
  rw [monsterNortonShortProjection_short]
  change (if f = d then v e else 0) = _
  by_cases h : d = f <;> simp [h, Ne.symm]

/-- Finite source-code equality suffices for every actual octad packet and unit pairing. -/
theorem monsterNortonForm_octad_unit_code (a b : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8)
    (hb : golayMaskWeight (golayEncodedMask b.val) = 8)
    (v : Fin 64 → ℝ) (e : Fin 64) :
    griessForm (monsterNortonOctadShortVector (monsterNortonOctadIndex a ha) v)
      (monsterNortonPureShort (Sum.inr (Sum.inl (monsterNortonOctadIndex b hb, e)))) =
        if a = b then v e else 0 := by
  rw [monsterNortonForm_octad_unit]
  simp only [monsterNortonOctadIndex_eq_iff]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
