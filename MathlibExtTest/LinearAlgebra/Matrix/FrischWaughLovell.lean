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

/-! For the block form, regress `y = (1, 7, 1, 3)` on an intercept and the two-column block
with columns `(0, 1, 2, 3)` and `(0, 1, 4, 9)`. The coefficients are `b = 2` and
`g = (3, -1)`. Regressing the block columns on the intercept gives their means
`U = (3/2, 7/2)`; the residualized Gram matrix is `[[5, 15], [15, 49]]`, and both sides of
the block identity equal `(0, -4)`. -/

/-- The intercept column for four observations. -/
def Ablock : Matrix (Fin 4) (Fin 1) ℝ := fun _ _ => 1

/-- The two-column regressor block `x` and `x²` at `x = 0, 1, 2, 3`. -/
def Zblock : Matrix (Fin 4) (Fin 2) ℝ :=
  Matrix.of ![![0, 0], ![1, 1], ![2, 4], ![3, 9]]

/-- The column means of `Zblock`, its regression coefficients on the intercept. -/
noncomputable def Ublock : Matrix (Fin 1) (Fin 2) ℝ := Matrix.of ![![3 / 2, 7 / 2]]

/-- The response for the block example. -/
def yblock : Fin 4 → ℝ := ![1, 7, 1, 3]

theorem Ablock_mulVec (c : ℝ) : Ablock *ᵥ ![c] = fun _ => c := by
  ext i
  simp [Ablock, mulVec, dotProduct]

theorem normal_Ablock :
    Ablockᵀ *ᵥ ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ
      (yblock - Ablock *ᵥ ![2] - Zblock *ᵥ ![3, -1])) = 0 := by
  ext i
  fin_cases i
  simp [Ablock_mulVec, Ablock, Zblock, yblock, mulVec, dotProduct, Fin.sum_univ_four,
    vecHead, vecTail]
  norm_num

theorem normal_Zblock :
    Zblockᵀ *ᵥ ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ
      (yblock - Ablock *ᵥ ![2] - Zblock *ᵥ ![3, -1])) = 0 := by
  ext i
  fin_cases i <;>
    simp [Ablock_mulVec, Zblock, yblock, mulVec, dotProduct, Fin.sum_univ_four,
      vecHead, vecTail] <;> norm_num

theorem resid_Zblock :
    Ablockᵀ * ((1 : Matrix (Fin 4) (Fin 4) ℝ) * (Zblock - Ablock * Ublock)) = 0 := by
  ext i j
  fin_cases i
  fin_cases j <;> simp [Ablock, Zblock, Ublock, Matrix.mul_apply, Fin.sum_univ_four] <;>
    norm_num

/-- The block theorem on the example. -/
example :
    ((Zblock - Ablock * Ublock)ᵀ * (1 : Matrix (Fin 4) (Fin 4) ℝ) *
      (Zblock - Ablock * Ublock)) *ᵥ ![3, -1] =
        (Zblock - Ablock * Ublock)ᵀ *ᵥ ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ yblock) :=
  frischWaughLovell_block transpose_one normal_Ablock normal_Zblock resid_Zblock

/-- The common value in the block identity is `(0, -4)`. -/
example :
    ((Zblock - Ablock * Ublock)ᵀ * (1 : Matrix (Fin 4) (Fin 4) ℝ) *
      (Zblock - Ablock * Ublock)) *ᵥ ![3, -1] = ![0, -4] := by
  ext i
  fin_cases i <;>
    simp [Ablock, Zblock, Ublock, mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_four] <;>
    norm_num

theorem gram_block :
    (Zblock - Ablock * Ublock)ᵀ * (1 : Matrix (Fin 4) (Fin 4) ℝ) *
        (Zblock - Ablock * Ublock) = !![5, 15; 15, 49] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ablock, Zblock, Ublock, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

/-- The block solved form recovers `g = (3, -1)`; the residual of `yblock` on the intercept
uses its mean `v = 3`. -/
example : ![3, -1] =
    ((Zblock - Ablock * Ublock)ᵀ * (1 : Matrix (Fin 4) (Fin 4) ℝ) *
      (Zblock - Ablock * Ublock))⁻¹ *ᵥ
        ((Zblock - Ablock * Ublock)ᵀ *ᵥ
          ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ (yblock - Ablock *ᵥ ![3]))) :=
  frischWaughLovell_block_eq_inv transpose_one normal_Ablock normal_Zblock resid_Zblock (by
    rw [gram_block]
    norm_num [Matrix.det_fin_two])

end MathlibExtTest.LinearAlgebra.Matrix.FrischWaughLovell
