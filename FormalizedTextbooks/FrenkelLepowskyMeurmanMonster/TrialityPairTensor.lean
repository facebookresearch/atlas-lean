/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Pair-matrix multiplication on the XYZ dictionary blocks.
The spin phases are derived from the actual pair lifts.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityBasisVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairSpinDictionary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

noncomputable def trialityYTensor (d : Fin 2048) (j : Fin 24)
    (t : SpinIndex) (i : Fin 24) : ℝ :=
  qSign (t 11) * (if (golayEncodedMask d.val).testBit j.val then -1 else 1) *
    (if spinDictionaryCode t = d then 1 else 0) * (if i = j then 1 else 0) / Real.sqrt 2

noncomputable def trialityZTensor (d : Fin 2048) (j : Fin 24)
    (t : SpinIndex) (i : Fin 24) : ℝ :=
  qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
    (if spinDictionaryCode t = d then 1 else 0) * (if i = j then 1 else 0) / Real.sqrt 2

theorem griessConwayEncode_X_basis (d : Fin 2048) (j : Fin 24) :
    griessConwayEncode (trialityXYZBasis 0 (finProdFinEquiv (d,j))) =
      (0, ((Pi.single (Sum.inr (Sum.inr (d,j))) 1 : GriessShortIndex → ℝ), 0)) := by
  rw [griessConwayEncode_XYZ_basis]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r
    rcases r with r | (r | ⟨e,i⟩)
    · simp
    · simp
    · simp only [Pi.single_apply, ite_true]
      have h : finProdFinEquiv (e,i) = finProdFinEquiv (d,j) ↔ (e,i) = (d,j) :=
        finProdFinEquiv.injective.eq_iff
      simp only [h, Sum.inr.injEq]
  · funext t i
    simp

theorem griessConwayEncode_Y_basis (d : Fin 2048) (j : Fin 24) :
    griessConwayEncode (trialityXYZBasis 1 (finProdFinEquiv (d,j))) =
      (0, (0, trialityYTensor d j)) := by
  rw [griessConwayEncode_XYZ_basis]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r
    rcases r with r | (r | r) <;> simp
  · funext t i
    simp only [Pi.single_apply, show (2 : Fin 3) ≠ 1 by decide, ite_false, ite_true]
    have h : finProdFinEquiv (spinDictionaryCode t,i) = finProdFinEquiv (d,j) ↔
        spinDictionaryCode t = d ∧ i = j := by
      rw [finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
    unfold trialityYTensor
    simp only [h, Pi.zero_apply, mul_zero, zero_add]
    by_cases hd : spinDictionaryCode t = d <;> by_cases hi : i = j
    all_goals simp [hd, hi]

theorem griessConwayEncode_Z_basis (d : Fin 2048) (j : Fin 24) :
    griessConwayEncode (trialityXYZBasis 2 (finProdFinEquiv (d,j))) =
      (0, (0, trialityZTensor d j)) := by
  rw [griessConwayEncode_XYZ_basis]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r
    rcases r with r | (r | r) <;> simp
  · funext t i
    simp only [Pi.single_apply, show (1 : Fin 3) ≠ 2 by decide, ite_false, ite_true]
    have h : finProdFinEquiv (spinDictionaryCode t,i) = finProdFinEquiv (d,j) ↔
        spinDictionaryCode t = d ∧ i = j := by
      rw [finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
    unfold trialityZTensor
    simp only [h, Pi.zero_apply, mul_zero, add_zero]
    by_cases hd : spinDictionaryCode t = d <;> by_cases hi : i = j
    all_goals simp [hd, hi]

set_option maxHeartbeats 4000000 in
-- This finite certificate concerns 2048 labels and twelve binary coordinates.
theorem golayLabel_low_add_omega : ∀ d : Fin 2048,
    golayLabelCoefficients ⟨d.val, by omega⟩ + Pi.single 11 1 =
      golayLabelCoefficients ⟨d.val + 2048, by omega⟩ := by
  decide +kernel

theorem golayLabel_high_add_omega (d : Fin 2048) :
    golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + Pi.single 11 1 =
      golayLabelCoefficients ⟨d.val, by omega⟩ := by
  rw [← golayLabel_low_add_omega d, add_assoc]
  have h : (Pi.single 11 1 : SpinIndex) + Pi.single 11 1 = 0 := by
    ext i
    simp only [Pi.add_apply, Pi.single_apply, Pi.zero_apply]
    split_ifs <;> decide
  rw [h, add_zero]

theorem spinDictionaryCode_add_omega (t : SpinIndex) :
    spinDictionaryCode (t + Pi.single 11 1) = spinDictionaryCode t := by
  rcases spinDictionaryIndex_cases t with h | h
  · rw [h, golayLabel_low_add_omega, spinDictionaryCode_high]
    simp only [spinDictionaryCode_low]
  · rw [h, golayLabel_high_add_omega, spinDictionaryCode_low]
    simp only [spinDictionaryCode_high]

theorem trialityYTensor_add_omega (d : Fin 2048) (j : Fin 24) (t : SpinIndex) (i : Fin 24) :
    trialityYTensor d j (t + Pi.single 11 1) i = -trialityYTensor d j t i := by
  simp only [trialityYTensor, spinDictionaryCode_add_omega, Pi.add_apply,
    Pi.single_apply, ite_true, qSign_add]
  rw [qSign_one]
  ring

theorem trialityZTensor_add_omega (d : Fin 2048) (j : Fin 24) (t : SpinIndex) (i : Fin 24) :
    trialityZTensor d j (t + Pi.single 11 1) i = trialityZTensor d j t i := by
  simp only [trialityZTensor, spinDictionaryCode_add_omega]

/-- The pair character is unchanged by the source all-one translation. -/
theorem golayPairCharacter_add_omega (a b : Fin 24) (t : SpinIndex) :
    qSign (golayEncoder (t + Pi.single 11 1) a +
      golayEncoder (t + Pi.single 11 1) b) =
      qSign (golayEncoder t a + golayEncoder t b) := by
  rw [map_add, golay_all_one]
  simp only [Pi.add_apply]
  apply congrArg qSign
  have h : (1 : ZMod 2) + 1 = 0 := by decide
  calc golayEncoder t a + 1 + (golayEncoder t b + 1) =
      (golayEncoder t a + golayEncoder t b) + (1 + 1) := by abel
    _ = _ := by rw [h, add_zero]

/-- Both spin indices over a source label give its physical pair character. -/
theorem golayPairCharacter_dictionary (a b : Fin 24) (t : SpinIndex) :
    qSign (golayEncoder t a + golayEncoder t b) =
      qSign (golayBooleanCast ((golayEncodedMask (spinDictionaryCode t).val).testBit a.val) +
        golayBooleanCast ((golayEncodedMask (spinDictionaryCode t).val).testBit b.val)) := by
  rcases spinDictionaryIndex_cases t with h | h
  · conv_lhs => rw [h, golayLabelEncoder_boolean, golayLabelEncoder_boolean]
  · conv_lhs => rw [h, ← golayLabel_low_add_omega, golayPairCharacter_add_omega,
        golayLabelEncoder_boolean, golayLabelEncoder_boolean]

/-- On a Y coordinate's support the actual pair character equals its source-label character. -/
theorem trialityYTensor_pair_character (p : Fin 276) (d : Fin 2048) (j : Fin 24)
    (t : SpinIndex) (i : Fin 24) :
    qSign (golayEncoder t (griessCoordinatePair p).1 +
      golayEncoder t (griessCoordinatePair p).2) * trialityYTensor d j t i =
      qSign (golayBooleanCast ((golayEncodedMask d.val).testBit
          (griessCoordinatePair p).1.val) +
        golayBooleanCast ((golayEncodedMask d.val).testBit
          (griessCoordinatePair p).2.val)) * trialityYTensor d j t i := by
  rw [golayPairCharacter_dictionary]
  by_cases h : spinDictionaryCode t = d
  · rw [h]
  · simp [trialityYTensor, h]

/-- The same actual pair character acts on a Z coordinate's support. -/
theorem trialityZTensor_pair_character (p : Fin 276) (d : Fin 2048) (j : Fin 24)
    (t : SpinIndex) (i : Fin 24) :
    qSign (golayEncoder t (griessCoordinatePair p).1 +
      golayEncoder t (griessCoordinatePair p).2) * trialityZTensor d j t i =
      qSign (golayBooleanCast ((golayEncodedMask d.val).testBit
          (griessCoordinatePair p).1.val) +
        golayBooleanCast ((golayEncodedMask d.val).testBit
          (griessCoordinatePair p).2.val)) * trialityZTensor d j t i := by
  rw [golayPairCharacter_dictionary]
  by_cases h : spinDictionaryCode t = d
  · rw [h]
  · simp [trialityZTensor, h]

/-- Binary source signs multiply by adding their exponents. -/
theorem qSign_boolean_add (x y : Bool) :
    qSign (golayBooleanCast x + golayBooleanCast y) =
      (if x then (-1 : ℝ) else 1) * (if y then -1 else 1) := by
  rw [qSign_add]
  cases x <;> cases y <;> simp [golayBooleanCast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
