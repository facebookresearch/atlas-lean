/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.PlugFlow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.NormNum

/-!
# Tests for the plug-flow balance in residence time

The rescaled derivative is checked at the outlet for a two-species state and nonunit flow.
The zero-volume case keeps the feed condition even with a nonzero production rate.
-/

open Chemistry.PlugFlow Set

example : HasDerivWithinAt (fun τ : ℝ ↦ (2 * τ, 3 * (2 * τ)))
    ((2, 6) : ℝ × ℝ) (Icc 0 2) 2 := by
  let c : ℝ → ℝ × ℝ := fun v ↦ (v, 3 * v)
  have h := (batch_in_residence_time (Q := 2) (V_R := 4) (by norm_num) (by norm_num)
    (fun _ : ℝ × ℝ ↦ (2, 6)) (0, 0)).1 c
  have h0 : c 0 = (0, 0) := by norm_num [c]
  have hd (v : ℝ) (_ : v ∈ Icc 0 4) :
      HasDerivWithinAt c ((2 : ℝ)⁻¹ • ((2, 6) : ℝ × ℝ)) (Icc 0 4) v := by
    have hv := ((hasDerivAt_id v).prodMk ((hasDerivAt_id v).const_mul 3)).hasDerivWithinAt
      (s := Icc (0 : ℝ) 4)
    norm_num [c, Prod.smul_mk, smul_eq_mul] at hv ⊢
    exact hv
  have hb := (h.mp ⟨h0, hd⟩).2 2 (by constructor <;> norm_num)
  norm_num [c] at hb ⊢
  exact hb

example (c : ℝ → ℝ) :
    (c 0 = 7 ∧ ∀ v ∈ Icc 0 0, HasDerivWithinAt c ((2 : ℝ)⁻¹ • (5 : ℝ)) (Icc 0 0) v) ↔
      c 0 = 7 :=
  (batch_in_residence_time (Q := 2) (V_R := 0) (by norm_num) le_rfl
    (fun _ : ℝ ↦ 5) 7).2.2.2 rfl c
