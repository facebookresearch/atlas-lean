/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.ThetaMethod
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.Ring.Basic

open MetaMathlibExt.ODE

-- The field depends on both its arguments, so evaluating it at the wrong endpoint matters.
example : IsThetaStep (fun t y : ℝ ↦ t + y) 0 0 (1 / 2) 1 (3 / 2) := by
  apply isThetaStep_zero_iff.mpr
  norm_num [smul_eq_mul]

example : IsThetaStep (fun t y : ℝ ↦ t + y) 1 0 (1 / 2) 1 (5 / 2) := by
  apply isThetaStep_one_iff.mpr
  norm_num [smul_eq_mul]

example : IsThetaStep (fun t y : ℝ ↦ t + y) (1 / 2) 0 (1 / 2) 1 (11 / 6) := by
  apply isThetaStep_half_iff.mpr
  norm_num [smul_eq_mul]

-- On [1, 5] with h = 2, the explicit Euler states for f(t, y) = t are 0, 2, 8.
example : ∃ u : Fin 3 → ℝ, u 0 = 0 ∧ ∀ n : Fin 2,
    IsThetaStep (fun t _ ↦ t) 0 (1 + (n.val : ℝ) * 2) 2 (u n.castSucc) (u n.succ) := by
  let u : Fin 3 → ℝ := fun i ↦ 2 * (i.val : ℝ) * (i.val : ℝ)
  have hu := (thetaMethod_uniformGrid_iff (fun t _ : ℝ ↦ t) 0 1 5 2 0 u).mpr (by
    constructor
    · norm_num [u]
    · intro n
      simp only [sub_zero, smul_eq_mul, u, Fin.val_castSucc, Fin.val_succ, Nat.cast_add,
        Nat.cast_one]
      norm_num
      ring1)
  have hh : (5 - 1 : ℝ) / (2 : ℕ) = 2 := by norm_num
  exact ⟨u, by simpa only [hh, Fin.val_castSucc] using hu⟩

-- A regular, genuinely implicit step has the single solution z = 2.
example (z : ℝ) : IsThetaStep (fun _ y : ℝ ↦ -y) (1 / 2) 0 1 6 z ↔ z = 2 := by
  have hd : (1 - 1 * (1 / 2) * (-1) : ℝ) ≠ 0 := by norm_num
  have hval : (((1 + 1 * (1 - 1 / 2) * (-1)) * 6) / (1 - 1 * (1 / 2) * (-1)) : ℝ) = 2 := by
    norm_num
  simpa only [neg_one_mul, hval] using
    (isThetaStep_linear_iff_eq (t := 0) (y := 6) (yNext := z) hd)

example : ∃! z, IsThetaStep (fun _ y : ℝ ↦ (-1) * y) (1 / 2) 0 1 6 z := by
  apply existsUnique_isThetaStep_linear_iff.mpr
  norm_num

-- At hθλ = 1 the equation is inconsistent for a nonzero starting value.
example : ¬ ∃ z, IsThetaStep (fun _ y : ℝ ↦ 2 * y) (1 / 2) 0 1 1 z := by
  have hd : (1 - 1 * (1 / 2) * 2 : ℝ) = 0 := by norm_num
  rintro ⟨z, hz⟩
  have hr := (isThetaStep_linear_singular_iff hd).mp hz
  norm_num at hr

-- For the same singular parameters but zero initial state, every z works.
example (z : ℝ) : IsThetaStep (fun _ y : ℝ ↦ 2 * y) (1 / 2) 0 1 0 z := by
  have hd : (1 - 1 * (1 / 2) * 2 : ℝ) = 0 := by norm_num
  exact (isThetaStep_linear_singular_iff hd).mpr (mul_zero _)
