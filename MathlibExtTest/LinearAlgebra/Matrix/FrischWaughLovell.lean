/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.FrischWaughLovell
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

open Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.FrischWaughLovell

/-! Ordinary least squares of `y = (1, 2, 4)` on an intercept and `z = (0, 1, 2)`: the normal
equations give intercept `b = 5/6` and slope `t = 3/2`; the residual of `z` on the intercept is
`z⊥ = (-1, 0, 1)`, and `t ⟪z⊥, z⊥⟫ = 3 = ⟪z⊥, y⟫`. -/

/-- The intercept column. -/
def A : Matrix (Fin 3) (Fin 1) ℝ := fun _ _ => 1

/-- The regressor of interest. -/
def z : Fin 3 → ℝ := ![0, 1, 2]

/-- The response. -/
def y : Fin 3 → ℝ := ![1, 2, 4]

theorem A_mulVec (c : ℝ) : A *ᵥ ![c] = fun _ => c := by
  ext i
  simp [A, mulVec, dotProduct]

theorem normal_A :
    Aᵀ *ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (y - A *ᵥ ![5 / 6] - (3 / 2 : ℝ) • z)) = 0 := by
  ext i
  fin_cases i
  simp [A_mulVec, y, z, mulVec, dotProduct, Fin.sum_univ_three, A, vecHead, vecTail]
  ring

theorem normal_z :
    z ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (y - A *ᵥ ![5 / 6] - (3 / 2 : ℝ) • z)) = 0 := by
  simp [A_mulVec, y, z, mulVec, dotProduct, Fin.sum_univ_three, vecHead, vecTail]
  ring

theorem resid_z : Aᵀ *ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (z - A *ᵥ ![1])) = 0 := by
  ext i
  fin_cases i
  simp [A_mulVec, z, mulVec, dotProduct, Fin.sum_univ_three, A]
  ring

/-- The theorem on the example: `t ⟪z⊥, z⊥⟫ = ⟪z⊥, y⟫`. -/
example : (3 / 2 : ℝ) * ((z - A *ᵥ ![1]) ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (z - A *ᵥ ![1]))) =
    (z - A *ᵥ ![1]) ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ y) :=
  frischWaughLovell (transpose_one) normal_A normal_z resid_z

/-- Both sides equal `3`. -/
example : (z - A *ᵥ ![1]) ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ y) = 3 := by
  simp [A_mulVec, y, z, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- The solved form recovers the slope from residualized data (residual of `y` on the intercept
uses `v = 7/3`). -/
example : (3 / 2 : ℝ) =
    (z - A *ᵥ ![1]) ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (y - A *ᵥ ![7 / 3])) /
      ((z - A *ᵥ ![1]) ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (z - A *ᵥ ![1]))) :=
  frischWaughLovell_eq_div transpose_one normal_A normal_z resid_z
    (by simp [A_mulVec, z, mulVec, dotProduct, Fin.sum_univ_three]; norm_num)

end MathlibExtTest.LinearAlgebra.Matrix.FrischWaughLovell
