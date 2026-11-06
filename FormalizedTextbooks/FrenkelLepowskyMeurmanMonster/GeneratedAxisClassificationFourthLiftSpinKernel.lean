/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftGaussKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftYColumn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftIntegerOperators

/-! Sixteen-term coordinate kernels of the genuine normalized flag spin operator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The diagonal Gaussian multiplies a coordinate unit by its original quadratic sign. -/
theorem generatedFourth_lift_gamma_unit (v : SpinIndex) :
    xiSpinGamma (Pi.single v 1) =
      (-qSign (generatedFourthLiftGammaPhaseFast v)) • (Pi.single v 1 : SpinSpace) := by
  classical
  funext t
  rw [generatedFourth_xi_gamma_apply, generatedFourth_lift_gamma_phase_fast]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h : t = v
  · simp only [h, ite_true]
  · simp only [h, ite_false, mul_zero]

/-- The actual Xi operator on a coordinate unit is a single grey-kernel coefficient. -/
theorem generatedFourth_lift_xi_unit (v t : SpinIndex) :
    xiSpinG (xiSpinGamma (Pi.single v 1)) t =
      (-qSign (generatedFourthLiftGammaPhaseFast v)) *
        (generatedFourthLiftGreyKernel (t + v) : ℝ) / 8 := by
  rw [generatedFourth_lift_gamma_unit, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, generatedFourth_lift_g_unit]
  ring

/-- The complete sixteen-term integer kernel retains both y82 changes and the Parker phase. -/
def generatedFourthLiftSpinKernel (t v : SpinIndex) : ℤ :=
  ∑ o : Fin 4, ∑ s : Fin 4,
    generatedFourthLiftYRowCoefficient t o *
    generatedFourthLiftIntSign (generatedFourthLiftPPhaseFast
      (generatedFourthFlagLiftCode.symm (generatedFourthLiftYRowAddress t o))) *
    generatedFourthLiftYRowCoefficient v s *
    (-generatedFourthLiftIntSign (generatedFourthLiftGammaPhaseFast
      (generatedFourthLiftYRowAddress v s))) *
    generatedFourthLiftGreyKernel
      (generatedFourthFlagLiftCode.symm (generatedFourthLiftYRowAddress t o) +
        generatedFourthLiftYRowAddress v s)

set_option maxHeartbeats 2000000 in
-- The actual product of normalizer operators requires unfolding its nested linear maps.
/-- The genuine normalized spin operator has exactly this sparse integer coordinate kernel. -/
theorem generatedFourth_lift_spin_unit (v t : SpinIndex) :
    monsterSourceY82Spin.val (generatedFourthFlagLiftSpin.val
      (xiSpinG (xiSpinGamma (monsterSourceY82Spin.val (Pi.single v 1))))) t =
        (generatedFourthLiftSpinKernel t v : ℝ) / 32 := by
  classical
  rw [generatedFourth_lift_y_column, map_sum]
  simp only [map_smul]
  rw [map_sum]
  simp only [map_smul]
  rw [generatedFourth_lift_y_row]
  change (∑ o : Fin 4, (generatedFourthLiftYRowCoefficient t o : ℝ) *
    (qSign (monsterMonomialQuadratic generatedFourthFlagLiftPhase
      (generatedFourthFlagLiftCode.symm (generatedFourthLiftYRowAddress t o))) *
      (∑ s : Fin 4, ((generatedFourthLiftYRowCoefficient v s : ℝ) / 2) •
        xiSpinG (xiSpinGamma (Pi.single (generatedFourthLiftYRowAddress v s) 1)))
          (generatedFourthFlagLiftCode.symm (generatedFourthLiftYRowAddress t o)))) / 2 = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, generatedFourth_lift_xi_unit,
    generatedFourth_lift_p_phase_fast, generatedFourthLiftSpinKernel, Int.cast_sum,
    Int.cast_mul, Int.cast_neg, generatedFourth_lift_int_sign_real]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro s _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
