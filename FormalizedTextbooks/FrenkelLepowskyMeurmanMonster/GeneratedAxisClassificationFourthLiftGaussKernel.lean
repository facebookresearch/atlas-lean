/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftGammaPhaseFast

/-! A Gaussian coordinate coefficient is determined by the unique actual grey translation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual off-diagonal grey pairing recovers translation coefficients. -/
def generatedFourthLiftGreyRecovery (w : SpinIndex) : XiGrayIndex :=
  xiGrayDual (fun i => spinDot (xiGrayCocodeBasis i) w)

/-- The recovery reads the genuine grey translation coefficients exactly. -/
theorem generatedFourth_lift_grey_recovery (a : XiGrayIndex) :
    generatedFourthLiftGreyRecovery (xiGrayCode a) = a := by
  simpa only [generatedFourthLiftGreyRecovery, xiGrayGammaProjection,
    xiGrayTranslation_translation] using xiGrayGammaProjection_translation a

/-- The actual grey translation has no repeated binary address. -/
theorem generatedFourth_lift_grey_injective : Function.Injective xiGrayCode := by
  intro a b h
  have he := congrArg generatedFourthLiftGreyRecovery h
  simpa only [generatedFourth_lift_grey_recovery] using he

/-- The exact single possible translation coefficient in the genuine Gaussian. -/
def generatedFourthLiftGreyKernel (w : SpinIndex) : ℤ :=
  if xiGrayCode (generatedFourthLiftGreyRecovery w) = w then
    xiGraySign (generatedFourthLiftGreyRecovery w) else 0

/-- The entire 64-term coordinate sum is its unique recovered grey coefficient. -/
theorem generatedFourth_lift_grey_kernel (w : SpinIndex) :
    (∑ a : XiGrayIndex, xiGraySign a * (if xiGrayCode a = w then (1 : ℤ) else 0)) =
      generatedFourthLiftGreyKernel w := by
  classical
  unfold generatedFourthLiftGreyKernel
  by_cases h : xiGrayCode (generatedFourthLiftGreyRecovery w) = w
  · rw [ite_eq_left h]
    rw [Finset.sum_eq_single (generatedFourthLiftGreyRecovery w)]
    · simp only [h, ite_true, mul_one]
    · intro a _ ha
      have hn : xiGrayCode a ≠ w := by
        intro he
        have hr := congrArg generatedFourthLiftGreyRecovery he
        rw [generatedFourth_lift_grey_recovery] at hr
        exact ha hr
      simp only [hn, ite_false, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro a _
    have hn : xiGrayCode a ≠ w := by
      intro he
      have hr := congrArg generatedFourthLiftGreyRecovery he
      rw [generatedFourth_lift_grey_recovery] at hr
      rw [← hr] at h
      exact h he
    simp only [hn, ite_false, mul_zero]

/-- A single ordinary spin coordinate has this exact genuine Gaussian output. -/
theorem generatedFourth_lift_g_unit (v t : SpinIndex) :
    xiSpinG (Pi.single v 1) t = (generatedFourthLiftGreyKernel (t + v) : ℝ) / 8 := by
  classical
  rw [generatedFourth_xi_g_apply]
  have htt : t + t = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (t i)
  have he (a : XiGrayIndex) : t + xiGrayCode a = v ↔ xiGrayCode a = t + v := by
    constructor
    · intro h
      have hh := congrArg (fun u => t + u) h
      simpa only [← add_assoc, htt, zero_add] using hh
    · intro h
      rw [h, ← add_assoc, htt, zero_add]
  simp only [Pi.single_apply, he]
  have h := congrArg (fun z : ℤ => (z : ℝ)) (generatedFourth_lift_grey_kernel (t + v))
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_one,
    Int.cast_zero, xiGraySign_real] at h
  rw [h]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
