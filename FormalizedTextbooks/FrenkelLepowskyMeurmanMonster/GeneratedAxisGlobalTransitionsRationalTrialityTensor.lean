/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerPrimitives

/-! Exact rational scaled tensor coordinates under the genuine original triality operator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The complete scaled tensor numerator keeps both original odd-short and incoming tensor terms. -/
def generatedAxisGlobalTrialityScaledTensorQ
    (C : GriessShortIndex → ℚ) (T : SpinIndex → Fin 24 → ℚ)
    (t : SpinIndex) (j : Fin 24) : ℚ :=
  let d := generatedAxisGlobalSpinLabelLow (generatedAxisGlobalSpinLabel t)
  let z : ℚ := if (golayEncodedMask d.val).testBit j.val then -1 else 1
  (generatedAxisGlobalIntSign (t 11) : ℚ) * z * C (Sum.inr (Sum.inr (d, j))) +
    (generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ℚ) *
      z * (T (golayLabelCoefficients ⟨d.val, by omega⟩) j -
        T (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) j) / 2

/-- Every physical coefficient follows from the entire original short and tensor constituents. -/
theorem generatedAxisGlobalTrialityScaledTensorQ_actual
    (x : GriessSpace) (C : GriessShortIndex → ℚ)
    (T : SpinIndex → Fin 24 → ℚ)
    (hC : ∀ r, (griessConwayEncode x).2.1 r = (C r : ℝ))
    (hT : ∀ t j, (griessConwayEncode x).2.2 t j = (T t j : ℝ) / Real.sqrt 2)
    (t : SpinIndex) (j : Fin 24) :
    (griessConwayEncode (sExtra x)).2.2 t j =
      (generatedAxisGlobalTrialityScaledTensorQ C T t j : ℝ) / Real.sqrt 2 := by
  rw [generatedAxisGlobalRawTrialityFormula_actual]
  change generatedAxisGlobalRawTrialityTensor (griessConwayEncode x) t j = _
  rw [generatedAxisGlobalRawTrialityTensor, hC, hT, hT]
  simp only [trialityYTensor, generatedAxisGlobalTrialityScaledTensorQ,
    generatedAxisGlobalSpinLabelLow_dictionary, generatedAxisGlobalSpinLabel_decode,
    Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_sub,
    Rat.cast_intCast, generatedAxisGlobalIntSign_real, apply_ite,
    Rat.cast_neg, Rat.cast_one, ↓reduceIte]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
