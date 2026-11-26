/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.DiscreteGronwall
import Mathlib.Tactic.NormNum

/-! # Examples for error propagation in perturbed iterations -/

open MetaMathlibExt

-- For the identity map and a constant unit perturbation, the error grows by one per step.
example : ‖(3 : ℝ) - 0‖ ≤ 3 := by
  obtain ⟨_, hExp, _⟩ := perturbed_iteration_gronwall
    (L := 1) (F := id) (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ))
    (x := fun _ => 0) (y := fun k => (k : ℝ)) (e := fun _ => 1) (τ := 1)
    (fun _ => rfl) (by intro k; simp) (by norm_num) 3
  calc
    ‖(3 : ℝ) - 0‖ ≤ Real.exp (0 * (3 : ℝ) * 1) * (‖(0 : ℝ) - 0‖ + 3 * 1) := by
      simpa only [Nat.cast_ofNat, Nat.cast_zero] using hExp 0 1 (le_refl 0) zero_le_one (by simp)
    _ = 3 := by norm_num

-- A zero Lipschitz constant erases the initial error after a single step.
example : ‖(1 : ℝ) - 0‖ ≤ 1 := by
  have hF : LipschitzWith 0 (fun _ : ℝ => (0 : ℝ)) :=
    LipschitzWith.of_dist_le_mul (by simp)
  obtain ⟨_, _, hContract⟩ := perturbed_iteration_gronwall hF
    (x := fun _ => 0) (y := fun k => if k = 0 then 5 else 1) (e := fun _ => 1) (τ := 1)
    (fun _ => rfl) (by intro k; simp) (by norm_num) 1
  convert hContract (by norm_num) using 1 <;> norm_num

-- The dropped sign condition would give an invalid bound, even for a constant map.
example : ∃ (F : ℝ → ℝ) (x y e : ℕ → ℝ),
    LipschitzWith (1 / 2) F ∧ (∀ k, x (k + 1) = F (x k)) ∧
    (∀ k, y (k + 1) = F (y k) + e k) ∧ (∀ k, ‖e k‖ ≤ 1) ∧
    Real.exp ((-1 / 2 : ℝ) * 1 * 1) * (‖y 0 - x 0‖ + 1 * 1) < ‖y 1 - x 1‖ := by
  refine ⟨fun _ => 0, fun _ => 0, fun k => if k = 1 then 1 else 0,
    fun k => if k = 0 then 1 else 0, ?_, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [dist_self]
    exact mul_nonneg (NNReal.coe_nonneg _) dist_nonneg
  · intro _
    rfl
  · intro k
    simp
  · intro k
    by_cases hk : k = 0 <;> simp [hk]
  · norm_num
