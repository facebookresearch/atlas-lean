/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisTranspositionCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddTensorFixed

/-! Exact full Griess norm of the genuine odd prototype and all original signed-short axes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- Every original signed-short Conway axis has full squared Griess norm 128. -/
theorem generatedAxisGlobal_conwayShortAxis_norm (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c) (conwayShortAxis r c) = 128 := by
  rw [griessForm_eq_conwayRawForm, conwayShortAxis_encode, conwayShortAxisRaw_form]
  have h : axisMatrixContraction (griessShortVector r) (conwayShortAxisRaw r c).1 = 32 := by
    simp only [axisMatrixContraction, conwayShortAxisRaw, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul]
    simp_rw [show ∀ i j : Fin 24,
      griessShortVector r i * (2 * (griessShortVector r i * griessShortVector r j)) *
        griessShortVector r j =
          2 * (griessShortVector r i * griessShortVector r i) *
            (griessShortVector r j * griessShortVector r j) by intro i j; ring]
    simp only [← Finset.mul_sum, griessShortVector_norm_sq]
    rw [← Finset.sum_mul, ← Finset.mul_sum, griessShortVector_norm_sq]
    norm_num
  rw [h]
  simp only [conwayShortAxisRaw, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
  nlinarith [qSign_sq c]

/-- The actual full odd prototype has the same exact squared Griess norm. -/
theorem generatedAxisGlobalOdd_norm : griessForm generatedOddAxis generatedOddAxis = 128 := by
  rw [generatedOddAxis, sExtra_preserves_griessForm, generatedAxisGlobal_conwayShortAxis_norm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
