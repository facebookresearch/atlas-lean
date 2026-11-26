/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.RenderingEquation
import Mathlib.Tactic.NormNum

/-! # Examples for the rendering equation -/

open scoped ENNReal
open ContinuousLinearMap

-- With no transport, emission is the unique solution and is the sum of the series.
example : HasSum (fun k : ℕ => ((0 : ℝ →L[ℝ] ℝ) ^ k) 2) 2 ∧
    (∀ J : ℝ, J = 2 + (0 : ℝ →L[ℝ] ℝ) J ↔ J = 2) := by
  obtain ⟨hs, hfix, _⟩ := rendering_equation_fixed_point_and_counterexample.1
    (0 : ℝ →L[ℝ] ℝ) 0 (by simp) zero_lt_one 2
  have hsum : (∑' k : ℕ, ((0 : ℝ →L[ℝ] ℝ) ^ k) 2) = 2 :=
    ((hfix 2).mp (by simp)).symm
  rw [hsum] at hs hfix
  exact ⟨hs, hfix⟩

-- Half transport gives solution 2, and the zeroth partial sum retains emission 1.
-- Exercise the truncation estimate through the rendering-equation theorem itself.
example :
    let T : ℝ →L[ℝ] ℝ := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
    (∑' k : ℕ, (T ^ k) 1) = 2 ∧
      (∑ k ∈ Finset.range (0 + 1), (T ^ k) 1) = 1 ∧
      ‖(∑' k : ℕ, (T ^ k) 1) - ∑ k ∈ Finset.range (0 + 1), (T ^ k) 1‖ ≤ 1 := by
  intro T
  have happ (x : ℝ) : T x = (1 / 2 : ℝ) * x := by simp [T]
  have hT : ‖T‖ ≤ 1 / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x => ?_)
    rw [happ, norm_mul, Real.norm_eq_abs (1 / 2 : ℝ)]
    norm_num
  obtain ⟨_, hfix, htrunc⟩ := rendering_equation_fixed_point_and_counterexample.1
    T (1 / 2) hT (by norm_num) 1
  have hsol : (∑' k : ℕ, (T ^ k) 1) = 2 := by
    exact ((hfix 2).mp (by rw [happ]; norm_num)).symm
  have hpartial : (∑ k ∈ Finset.range (0 + 1), (T ^ k) 1) = 1 := by
    simp only [Nat.zero_add, Finset.sum_range_one, pow_zero, one_apply_eq_self]
  have hbound : (1 / 2 : ℝ) ^ (0 + 1 : ℕ) * ‖(1 : ℝ)‖ / (1 - 1 / 2) = 1 := by
    norm_num
  have herr := htrunc 0
  rw [hbound] at herr
  exact ⟨hsol, hpartial, herr⟩

-- The diagonal counterexample kills coordinate zero but still has no bounded solution.
example : ∃ (T : lp (fun _ : ℕ => ℝ) ⊤ →L[ℝ] lp (fun _ : ℕ => ℝ) ⊤)
    (E : lp (fun _ : ℕ => ℝ) ⊤),
    (∀ x, (T x : ℕ → ℝ) 0 = 0) ∧ ‖T‖ = 1 ∧ ¬ ∃ I, I = E + T I := by
  obtain ⟨T, E, hdiag, _, hnorm, hnosol⟩ := rendering_equation_fixed_point_and_counterexample.{0}.2
  exact ⟨T, E, fun x => by simpa using hdiag x 0, hnorm, hnosol⟩
