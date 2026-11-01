/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftIntegerBridge

/-! The composed integer spin numerator is the genuine fully phased normalized flag lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem map_divide (L : Module.End ℝ SpinSpace) (f : SpinSpace)
    (D : ℝ) (t : SpinIndex) : L (fun u => f u / D) t = L f t / D := by
  have hf : (fun u => f u / D) = D⁻¹ • f := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hf, map_smul]
  change D⁻¹ * L f t = _
  rw [div_eq_mul_inv, mul_comm]

private theorem y_scaled (f : SpinIndex → ℤ) (D : ℝ) :
    monsterSourceY82Spin.val (fun u => (f u : ℝ) / D) =
      fun u => (generatedFourthLiftIntY f u : ℝ) / (2 * D) := by
  funext t
  have h := map_divide monsterSourceY82Spin.val.toLinearMap (fun u => (f u : ℝ)) D t
  change monsterSourceY82Spin.val (fun u => (f u : ℝ) / D) t =
    monsterSourceY82Spin.val (fun u => (f u : ℝ)) t / D at h
  rw [generatedFourth_lift_y_integer] at h
  simpa only [div_div] using h

private theorem gamma_scaled (f : SpinIndex → ℤ) (D : ℝ) :
    xiSpinGamma (fun u => (f u : ℝ) / D) =
      fun u => (generatedFourthLiftIntGamma f u : ℝ) / D := by
  funext t
  have h := map_divide xiSpinGamma (fun u => (f u : ℝ)) D t
  rw [generatedFourth_lift_gamma_integer] at h
  exact h

private theorem g_scaled (f : SpinIndex → ℤ) (D : ℝ) :
    xiSpinG (fun u => (f u : ℝ) / D) =
      fun u => (generatedFourthLiftIntG f u : ℝ) / (8 * D) := by
  funext t
  have h := map_divide xiSpinG (fun u => (f u : ℝ)) D t
  rw [generatedFourth_lift_g_integer] at h
  simpa only [div_div] using h

private theorem p_scaled (f : SpinIndex → ℤ) (D : ℝ) :
    generatedFourthFlagLiftSpin.val (fun u => (f u : ℝ) / D) =
      fun u => (generatedFourthLiftIntP f u : ℝ) / D := by
  funext t
  have h := map_divide generatedFourthFlagLiftSpin.val.toLinearMap
    (fun u => (f u : ℝ)) D t
  change generatedFourthFlagLiftSpin.val (fun u => (f u : ℝ) / D) t =
    generatedFourthFlagLiftSpin.val (fun u => (f u : ℝ)) t / D at h
  rw [generatedFourth_lift_p_integer] at h
  exact h

set_option maxHeartbeats 2000000 in
-- Explicit operator products require unfolding the actual nested fiber and normalizer projections.
/-- The exact actual spin lift on any integer state has denominator thirty-two. -/
theorem generatedFourth_lift_spin_numerator (f : SpinIndex → ℤ) (D : ℝ) :
    generatedFourthFlagNormalizedLift.val.1.val (fun u => (f u : ℝ) / D) =
      fun u => (generatedFourthLiftIntY (generatedFourthLiftIntP
        (generatedFourthLiftIntG
          (generatedFourthLiftIntGamma (generatedFourthLiftIntY f)))) u : ℝ) /
          (32 * D) := by
  change monsterSourceY82Spin.val (generatedFourthFlagLiftSpin.val
    (xiSpinG (xiSpinGamma (monsterSourceY82Spin.val (fun u => (f u : ℝ) / D))))) = _
  rw [y_scaled, gamma_scaled, g_scaled, p_scaled, y_scaled]
  funext u
  congr 1
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
