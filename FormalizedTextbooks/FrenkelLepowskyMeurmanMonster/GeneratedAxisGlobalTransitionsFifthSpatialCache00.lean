/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthSpatialCache00Checks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMatrixCoordinates

/-! Complete original source checks for the root-zero rational spatial matrix cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All seven checked source stages identify the entire original spatial word matrix. -/
theorem generatedAxisGlobalFifthSpatialCache00_word_actual :
    generatedAxisGlobalFifthSpatialWordMatrix 0 =
      generatedAxisGlobalFifthSpatialCache00State 7 := by
  let e := fun j => generatedAxisGlobalFifthSpatialStageMatrix 0
    ⟨j % 7, Nat.mod_lt _ (by decide)⟩
  let u := fun j => generatedAxisGlobalFifthSpatialCache00State
    ⟨j % 8, Nat.mod_lt _ (by decide)⟩
  have hs : ∀ j, j < 7 → e j * u j = u (j + 1) := by
    intro j hj
    have hh := generatedAxisGlobalFifthSpatialCache00_steps ⟨j, hj⟩
    rw [← generatedAxisGlobalFifthSpatialCache00_stage_actual] at hh
    simpa only [e, u, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, Nat.mod_eq_of_lt hj,
      Nat.mod_eq_of_lt (show j < 8 by omega),
      Nat.mod_eq_of_lt (show j + 1 < 8 by omega)] using hh
  have he := generatedAxisGlobalWordChain_action e u 7 hs
  change generatedAxisGlobalFifthSpatialWordMatrix 0 *
    generatedAxisGlobalFifthSpatialCache00State 0 =
      generatedAxisGlobalFifthSpatialCache00State 7 at he
  simpa only [generatedAxisGlobalFifthSpatialCache00_initial, mul_one] using he

/-- The exact cached rational matrix is the entire actual fifth-axis word matrix constituent. -/
theorem generatedAxisGlobalFifthSpatialCache00_matrix_actual :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord 0) generatedFifthAxis)).1 =
        generatedAxisGlobalFifthSpatialCache00Matrix.map (Rat.castHom ℝ) := by
  rw [generatedAxisGlobalFifthRootMatrixQ_actual]
  apply congrArg (fun A : Matrix (Fin 24) (Fin 24) ℚ => A.map (Rat.castHom ℝ))
  ext i j
  rw [generatedAxisGlobalFifthRootMatrixQ, generatedAxisGlobalFifthSpatialCache00_word_actual,
    Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  exact generatedAxisGlobalFifthSpatialCache00_matrix_checked i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
