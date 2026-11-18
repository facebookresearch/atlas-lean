/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.FiniteIntervalSublevel

open MathlibExt.Analysis.ODE

-- Decreasing example on `[2, 3]`: `V = id`, `γ t = -t`,
-- orbital derivative `-1`. Antitonicity gives
-- `(V ∘ γ) 3 ≤ (V ∘ γ) 2`, that is `-3 ≤ -2`.
example : (-3 : ℝ) ≤ -2 :=
  finite_interval_antitoneOn_v_comp (V := (id : ℝ → ℝ)) (γ := fun t : ℝ => -t)
    (f := fun _ _ => (-1 : ℝ)) (a := 2) (b := 3)
    (continuous_id.comp continuous_neg).continuousOn
    (fun t _ => hasDerivAt_neg t) (fun _ _ => differentiableAt_id)
    (by
      intro t _
      rw [fderiv_id]
      norm_num)
    ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num)

-- The sublevel statement: with `c = -2`, the initial bound
-- `V (γ 2) = -2 ≤ -2` persists; `γ 3 = -3` and
-- `γ (5 / 2) = -5 / 2` stay in `{x | V x ≤ -2}`.
example : (fun t : ℝ => -t) 3 ∈ {x : ℝ | id x ≤ -2} :=
  finite_interval_mapsTo_sublevel (V := (id : ℝ → ℝ)) (γ := fun t : ℝ => -t)
    (f := fun _ _ => (-1 : ℝ)) (a := 2) (b := 3) (by norm_num)
    (continuous_id.comp continuous_neg).continuousOn
    (fun t _ => hasDerivAt_neg t) (fun _ _ => differentiableAt_id)
    (by
      intro t _
      rw [fderiv_id]
      norm_num)
    (c := -2) le_rfl
    ⟨by norm_num, le_rfl⟩

example : (fun t : ℝ => -t) (5 / 2) ∈ {x : ℝ | id x ≤ -2} :=
  finite_interval_mapsTo_sublevel (V := (id : ℝ → ℝ)) (γ := fun t : ℝ => -t)
    (f := fun _ _ => (-1 : ℝ)) (a := 2) (b := 3) (by norm_num)
    (continuous_id.comp continuous_neg).continuousOn
    (fun t _ => hasDerivAt_neg t) (fun _ _ => differentiableAt_id)
    (by
      intro t _
      rw [fderiv_id]
      norm_num)
    (c := -2) le_rfl
    ⟨by norm_num, by norm_num⟩

-- Singleton interval `a = b = 5`: antitonicity is `-5 ≤ -5`.
example : (-5 : ℝ) ≤ -5 :=
  finite_interval_antitoneOn_v_comp (V := (id : ℝ → ℝ)) (γ := fun t : ℝ => -t)
    (f := fun _ _ => (-1 : ℝ)) (a := 5) (b := 5)
    (continuous_id.comp continuous_neg).continuousOn
    (fun t _ => hasDerivAt_neg t) (fun _ _ => differentiableAt_id)
    (by
      intro t _
      rw [fderiv_id]
      norm_num)
    ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩ le_rfl

-- The sign hypothesis cannot be dropped: for `γ t = t`,
-- `V = id`, `f = 1` on `[0, 1]`, the orbital derivative is
-- `1 > 0`, so the nonpositivity hypothesis fails (and the
-- would-be conclusion at `t = 1` is `1 ≤ 0`, false).
example :
    ¬ ∀ t ∈ Set.Ioo (0 : ℝ) 1, fderiv ℝ (id : ℝ → ℝ) t (1 : ℝ) ≤ 0 := by
  intro h
  have h1 := h (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [fderiv_id] at h1
  simp only [ContinuousLinearMap.id_apply] at h1
  norm_num at h1

#print axioms finite_interval_antitoneOn_v_comp
#print axioms finite_interval_mapsTo_sublevel
