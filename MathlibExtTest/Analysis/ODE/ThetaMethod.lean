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

-- For y' = y², implicit Euler with h = 1 and y₀ = 0 asks for z = z².
example : IsThetaStep (fun _ y : ℝ ↦ y * y) 1 0 1 0 0 ∧
    IsThetaStep (fun _ y : ℝ ↦ y * y) 1 0 1 0 1 := by
  constructor <;> apply isThetaStep_one_iff.mpr <;> norm_num [smul_eq_mul]
