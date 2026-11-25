/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Sturm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for Sturm's theorem -/

namespace MathlibExtTest.Algebra.Sturm

open Polynomial MathlibExt.Algebra.SturmWanted.Algebra

example : sturmChain (0 : ℝ[X]) = [0] := by simp [sturmChain, sturmAux]

example : signChanges [0, -2, 0, 0, 3, 0, -1, 0] = 2 := by
  norm_num [signChanges, List.filter]

-- The value at a simple root already has the variation on its right.
example : sigma X (-1) = 1 ∧ sigma X 0 = 0 ∧ sigma X 1 = 0 := by
  norm_num [sigma, sturmChain, sturmAux, signChanges, List.filter]

-- The chain of x²/2 - 1 is [x²/2 - 1, x, 1]. At the endpoint 0 the middle entry vanishes.
private noncomputable def quadratic : ℝ[X] := C (1 / 2 : ℝ) * X ^ 2 - 1

private theorem derivative_quadratic : quadratic.derivative = X := by
  simp [quadratic, derivative_mul, ← mul_assoc]
  simpa only [map_mul, map_add, map_one] using
    congrArg (C : ℝ → ℝ[X]) (show (2 : ℝ)⁻¹ * (1 + 1) = 1 by norm_num)

private theorem quadratic_chain : sturmChain quadratic = [quadratic, X, 1] := by
  have hr : quadratic % X = -1 := by
    simpa [quadratic] using mod_X_sub_C_eq_C_eval quadratic 0
  simp [sturmChain, derivative_quadratic, sturmAux, hr]
  cases quadratic.natDegree <;> simp [sturmAux]

example : (quadratic.roots.toFinset.filter fun x => -2 < x ∧ x < 0).card = 1 := by
  have hsq : Squarefree quadratic := by
    apply Separable.squarefree
    refine ⟨-1, C (1 / 2 : ℝ) * X, ?_⟩
    rw [derivative_quadratic]
    unfold quadratic
    ring
  rw [sturm quadratic hsq (by norm_num) (by norm_num [quadratic]) (by norm_num [quadratic])]
  simp only [sigma, quadratic_chain, List.map_cons, List.map_nil]
  norm_num [quadratic, signChanges, List.filter]

end MathlibExtTest.Algebra.Sturm
