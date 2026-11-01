/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftIntegerOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftGauss

/-! The integer operator numerators are tied to the genuine real spin operators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The integer y82 numerator is exactly the original real four-term numerator. -/
theorem generatedFourth_lift_int_y_real (f : SpinIndex → ℤ) (t : SpinIndex) :
    (generatedFourthLiftIntY f t : ℝ) =
      generatedFourthLiftYNumerator (fun u => (f u : ℝ)) t := by
  simp only [generatedFourthLiftIntY, generatedFourthLiftYNumerator,
    Int.cast_add, Int.cast_mul, generatedFourth_lift_int_sign_real,
    ← generatedFourth_lift_y_phase_fast]

/-- The actual y82 spin operator has the checked integer numerator with denominator two. -/
theorem generatedFourth_lift_y_integer (f : SpinIndex → ℤ) (t : SpinIndex) :
    monsterSourceY82Spin.val (fun u => (f u : ℝ)) t =
      (generatedFourthLiftIntY f t : ℝ) / 2 := by
  rw [generatedFourth_lift_y_numerator, generatedFourth_lift_int_y_real]

/-- The actual cocode Gaussian has the stated exact integer diagonal sign. -/
theorem generatedFourth_lift_gamma_integer (f : SpinIndex → ℤ) (t : SpinIndex) :
    xiSpinGamma (fun u => (f u : ℝ)) t = (generatedFourthLiftIntGamma f t : ℝ) := by
  rw [generatedFourth_xi_gamma_apply]
  simp only [generatedFourthLiftIntGamma, Int.cast_mul, Int.cast_neg,
    generatedFourth_lift_int_sign_real, generatedFourth_lift_gamma_phase_fast]

/-- The actual code Gaussian has the stated integer 64-shift numerator and denominator eight. -/
theorem generatedFourth_lift_g_integer (f : SpinIndex → ℤ) (t : SpinIndex) :
    xiSpinG (fun u => (f u : ℝ)) t = (generatedFourthLiftIntG f t : ℝ) / 8 := by
  rw [generatedFourth_xi_g_apply]
  simp only [generatedFourthLiftIntG, Int.cast_sum, Int.cast_mul, xiGraySign_real]
  ring

/-- The actual Parker correction uses the integer phase at the inverse coefficient address. -/
theorem generatedFourth_lift_p_integer (f : SpinIndex → ℤ) (t : SpinIndex) :
    generatedFourthFlagLiftSpin.val (fun u => (f u : ℝ)) t =
      (generatedFourthLiftIntP f t : ℝ) := by
  change qSign (monsterMonomialQuadratic generatedFourthFlagLiftPhase
    (generatedFourthFlagLiftCode.symm t)) * (f (generatedFourthFlagLiftCode.symm t) : ℝ) = _
  simp only [generatedFourthLiftIntP, Int.cast_mul, generatedFourth_lift_int_sign_real,
    generatedFourth_lift_p_phase_fast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
