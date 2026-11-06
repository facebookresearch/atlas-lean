/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerTensorPackedPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorMatrixReplayGeneric

/-! Genuine two-fixer integer tensor fixation from complete physical and circuit certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The two actual physical source denominators are nonzero, independently of any orbit count. -/
theorem generatedTenth_two_fixer_tensor_denominator_ne_zero :
    ∀ g : Fin 2, generatedTenthTwoFixerTensorDenominator g ≠ 0 := by
  decide +kernel

/-- Genuine physical matrices and whole spin circuits fix the complete retained integer tensor. -/
theorem generatedTenth_two_fixer_tensor_integer_fix
    (hphysical : GeneratedTenthTwoFixerTensorPhysicalCondition)
    (hstart : GeneratedTenthTwoFixerTensorStartCondition)
    (hpairs : GeneratedTenthTwoFixerTensorPairCondition)
    (hfinish : GeneratedTenthTwoFixerTensorFinishCondition) (g : Fin 2) :
    localTensorRepresentation (generatedTenthTwoFixerTensorFiber g)
      (fun t j => (generatedTenthTwoFixerTensorInput (nortonUIntegerLabel t) j : ℝ)) =
        (fun t j => (generatedTenthTwoFixerTensorInput (nortonUIntegerLabel t) j : ℝ)) := by
  have hspin (j : Fin 24) : (generatedTenthTwoFixerTensorFiber g).val.1.val
      (nortonUIntegerEmbed (fun n => ∑ k : Fin 24,
        generatedTenthTwoFixerTensorNumerator g j k * generatedTenthTwoFixerTensorInput n k)) =
        nortonUIntegerEmbed (fun n => (generatedTenthTwoFixerTensorDenominator g : ℤ) *
          generatedTenthTwoFixerTensorInput n j) := by
    have h := generatedTenth_two_fixer_tensor_column_circuit hstart hpairs hfinish g j
    have hs : (generatedTenthTwoFixerTensorFiber g).val.1 = generatedTenthTwoFixerTensorSpin g := by
      fin_cases g <;> rfl
    rw [hs]
    refine h.trans ?_
    ext t
    simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  funext t i
  have h := generatedTwelfth_tensor_matrix_column_replay (generatedTenthTwoFixerTensorFiber g)
    (generatedTenthTwoFixerTensorNumerator g) (generatedTenthTwoFixerTensorDenominator g)
    (generatedTenth_two_fixer_tensor_denominator_ne_zero g) (hphysical g)
    generatedTenthTwoFixerTensorInput
    (fun n j => (generatedTenthTwoFixerTensorDenominator g : ℤ) *
      generatedTenthTwoFixerTensorInput n j) hspin t i
  rw [h]
  simp only [Int.cast_mul, Int.cast_natCast]
  have hd : (generatedTenthTwoFixerTensorDenominator g : ℝ) ≠ 0 := by
    exact_mod_cast generatedTenth_two_fixer_tensor_denominator_ne_zero g
  exact mul_div_cancel_left₀ _ hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
