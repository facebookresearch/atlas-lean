/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddRootLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPairCoordinates

/-! Exact original signs of the preferred inputs for the 56 odd-output rows.
The octad Fourier diagonal signs are retained before any spin-state binding. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The input signs include the original triality octad diagonal sign. -/
def generatedFourthOddRootInputPhase (j : Fin 56) : ZMod 2 :=
  match generatedFourthOddRootInputData j with
  | Sum.inl (s, _, _) => if s = 0 then 0 else 1
  | Sum.inr e => if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then 1 else 0

/-- Check that every recorded coordinate-pair input belongs to the selected octad. -/
def generatedFourthOddRootInputSupport (j : Fin 56) : Bool :=
  match generatedFourthOddRootInputData j with
  | Sum.inl (_, a, b) => Nat.testBit 0xcccc00 a.val && Nat.testBit 0xcccc00 b.val
  | Sum.inr _ => true

/-- All listed input pairs genuinely lie in the selected octad. -/
theorem generatedFourthOddRootInputSupport_eq : ∀ j : Fin 56,
    generatedFourthOddRootInputSupport j = true := by
  decide +kernel

/-- The original unsigned octad physical coordinate on its support. -/
theorem generatedFourth_original_octad_vector (i : Fin 24)
    (hi : Nat.testBit 0xcccc00 i.val = true) :
    griessShortVector (Sum.inr (Sum.inl (generatedFourthOctad, 0))) i = 2 / Real.sqrt 8 := by
  have hm : griessOctadSignMask generatedFourthOctad 0 = 0 := by
    simp [griessOctadSignMask, show trialityEvenMask 0 = 0 from by decide]
  simp only [griessShortVector, griessShortIntegral, generatedFourthOctad_mask, hm,
    Nat.zero_testBit, hi]
  norm_num

/-- Original pair-short coefficients on the selected octad have the stated preferred signs. -/
theorem generatedFourth_original_pair_coefficient (s : Fin 2) (a b : Fin 24)
    (hlt : a < b) (ha : Nat.testBit 0xcccc00 a.val = true)
    (hb : Nat.testBit 0xcccc00 b.val = true) :
    (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
        (Sum.inl (s, griessPairIndex a b (ne_of_lt hlt))) =
      qSign (if s = 0 then 0 else 1) := by
  rw [generatedAxis_triality_octad_pair_coordinate, griessPairIndex_coordinates, ite_eq_left hlt]
  rw [generatedFourth_original_octad_vector a ha, generatedFourth_original_octad_vector b hb]
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  by_cases hs0 : s = 0
  · simp only [hs0, ite_true, qSign_zero]
    field_simp
    nlinarith [hs]
  · simp only [hs0, ite_false, qSign_one]
    field_simp
    nlinarith [hs]

/-- Original octad-short Fourier coefficients include the actual diagonal sign. -/
theorem generatedFourth_original_octad_coefficient (e : Fin 64) :
    (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
        (Sum.inr (Sum.inl (generatedFourthOctad, e))) =
      qSign (if trialityBitWeight8 (trialityEvenMask e) / 2 % 2 = 0 then 1 else 0) := by
  simp only [griessConwayEncode, sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  change trialityOctadAction
    ((trialityBlocksEquiv (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)).2.2.1 generatedFourthOctad) e = _
  have hr : (trialityBlocksEquiv (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)).2.2.1 generatedFourthOctad =
      (-8 : ℝ) • Pi.single 0 1 := by
    funext k
    by_cases hk : k = 0 <;>
      simp [conwayShortAxis, griessConwayDecode, conwayShortAxisRaw, Pi.single_apply, hk]
  rw [hr, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [monsterSourceTriality_octad_basis]
  have hh : ∀ k : Fin 64, trialityHadamard 0 k = 1 := by decide +kernel
  simp only [monsterSourceTrialityOctadRows, hh, trialityIntegerDiagonal]
  split_ifs <;> norm_num [qSign_zero, qSign_one]

/-- Each of the 56 input labels has its exact original signed coefficient. -/
theorem generatedFourth_original_input_coefficient (j : Fin 56) :
    (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
        (generatedFourthOddRootInputLabel j) = qSign (generatedFourthOddRootInputPhase j) := by
  have hl := generatedFourthOddRootInputData_lt j
  have hs := generatedFourthOddRootInputSupport_eq j
  unfold generatedFourthOddRootInputLabel
  split
  · rename_i s a b h
    simp only [h] at hl
    simp only [generatedFourthOddRootInputSupport, h, Bool.and_eq_true] at hs
    simpa only [generatedFourthOddRootInputPhase, h] using
      generatedFourth_original_pair_coefficient s a b hl hs.1 hs.2
  · rename_i e h
    simpa only [generatedFourthOddRootInputPhase, h] using
      generatedFourth_original_octad_coefficient e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
