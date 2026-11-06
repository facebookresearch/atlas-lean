/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorActual

/-! A computable integer numerator for the actual fourth axis tensor. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The integer sign with the same value as the original real spin sign. -/
def generatedFourthLiftIntSign (c : ZMod 2) : ℤ := if c = 0 then 1 else -1

/-- The integer sign embeds into the genuine real spin sign. -/
theorem generatedFourth_lift_int_sign_real (c : ZMod 2) :
    (generatedFourthLiftIntSign c : ℝ) = qSign c := by
  simp [generatedFourthLiftIntSign, qSign]

/-- The exact four-point common plane, as a decidable predicate on actual spin labels. -/
def generatedFourthLiftPlane (t : SpinIndex) : Prop :=
  t = 0 ∨ t = golayLabelCoefficients 14 ∨ t = golayLabelCoefficients 2048 ∨
    t = golayLabelCoefficients 14 + golayLabelCoefficients 2048

/-- The explicit four-point predicate has a computable equality decision. -/
instance (t : SpinIndex) : Decidable (generatedFourthLiftPlane t) :=
  inferInstanceAs (Decidable (t = 0 ∨ t = golayLabelCoefficients 14 ∨
    t = golayLabelCoefficients 2048 ∨ t = golayLabelCoefficients 14 + golayLabelCoefficients 2048))

/-- The plane predicate is the genuine already proved affine plane membership. -/
theorem generatedFourth_lift_plane_iff (t : SpinIndex) :
    generatedFourthLiftPlane t ↔ t ∈ generatedAxisFourthQAffineParameterPlane :=
  (generatedAxisFourthQAffineParameter_plane_mem_four_iff t).symm

/-- The complete actual tensor numerator with its original signs and all twenty-eight states. -/
def generatedFourthLiftIntegerTensor (t : SpinIndex) (i : Fin 24) : ℤ :=
  ∑ k : Fin 28, if i = generatedFourthQAffineTensorColumns k then
    if generatedFourthLiftPlane
        (t + generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex k))
    then generatedFourthLiftIntSign (generatedFourthQAffineTensorScalePhases k +
      spinDot (generatedAxisFourthQAffineParameterCharacters
        (generatedFourthQAffineTensorFamilyIndex k))
        (t + generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex k)))
    else 0 else 0

/-- The computable numerator equals the actual original tensor with its exact sqrt-two scale. -/
theorem generatedFourth_lift_integer_tensor (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedFourthAxis).2.2 t i =
      (generatedFourthLiftIntegerTensor t i : ℝ) / Real.sqrt 2 := by
  rw [generatedFourthQAffineTensor_actual]
  simp only [generatedFourthQAffineTensorPacked, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, generatedFourthLiftIntegerTensor, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  simp only [generatedFourthQAffineTensorState, generatedAxisFourthQAffineSpinState,
    ← generatedFourth_lift_plane_iff, Int.cast_ite, Int.cast_zero]
  split_ifs <;> simp only [generatedFourth_lift_int_sign_real, qSign_add, div_mul_eq_mul_div,
    mul_zero, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
