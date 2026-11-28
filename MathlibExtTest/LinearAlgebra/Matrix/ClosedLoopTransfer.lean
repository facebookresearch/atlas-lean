/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.ClosedLoopTransfer
import Mathlib.Algebra.Field.Rat
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for closed-loop transfer maps -/

open Matrix
open MetaMathlibExt.Matrix

namespace MathlibExtTest.ClosedLoopTransfer

private def plant : Matrix (Fin 2) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 0]
private def controller : Matrix (Fin 3) (Fin 2) ℚ := !![1, 1; 0, 2; 3, 4]

private theorem plant_loop_isUnit : IsUnit (1 + plant * controller) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_two]
  norm_num [plant, controller, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
    Fin.sum_univ_three]

/-- On a `2 × 3` plant the formulas give the concrete error, control and output vectors.
Verify the vectors directly against the loop equations, then use uniqueness. -/
example :
    let S := (1 + plant * controller)⁻¹
    (S *ᵥ ![5, 3], (controller * S) *ᵥ ![5, 3], (plant * controller * S) *ᵥ ![5, 3]) =
      (![2, 1], ![3, 2, 10], ![3, 2]) := by
  obtain ⟨hunique, hformula, _, _⟩ :=
    closed_loop_transfer_existsUnique plant controller plant_loop_isUnit ![5, 3]
  apply hunique.unique hformula
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;>
    norm_num [plant, controller, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three]

/-- The feedback equation has a unique solution also for complex-valued transfer matrices. -/
example (G : Matrix (Fin 2) (Fin 3) ℂ) (K : Matrix (Fin 3) (Fin 2) ℂ)
    (h : IsUnit (1 + G * K)) (r : Fin 2 → ℂ) :
    ∃! x : (Fin 2 → ℂ) × (Fin 3 → ℂ) × (Fin 2 → ℂ),
      x.1 = r - x.2.2 ∧ x.2.1 = K *ᵥ x.1 ∧ x.2.2 = G *ᵥ x.2.1 :=
  (closed_loop_transfer_existsUnique G K h r).1

end MathlibExtTest.ClosedLoopTransfer
