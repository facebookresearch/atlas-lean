/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Finance.FiniteLiquidation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Domains.Economics.Finance.FiniteLiquidation

-- Exact excess at every signed perturbation of the optimal middle inventory.
example (z : ℝ) : cost 2 3 (3 / 2) ![8, 2 + z, 0] = 264 + 6 * z ^ 2 := by
  simp [cost, Fin.sum_univ_succ]
  ring

-- Identify the theorem's witness, not just a solution of an unrelated scalar quadratic.
example : ∃ p : Fin 3 → ℝ, p = ![8, 2, 0] ∧ cost 2 3 (3 / 2) p = 264 ∧
    ∀ x : Fin 3 → ℝ, x 0 = 8 → x 2 = 0 → (cost 2 3 (3 / 2) x = 264 ↔ x = p) := by
  obtain ⟨p, h₀, h₂, hmin, he⟩ := exists_unique_optimal_path (N := 2) (Δ := 2) (η := 3)
    (κ := 3 / 2) (by decide) (by norm_num) (by norm_num) (by norm_num) 8
  have hm := he 1 (by decide) (by decide)
  change 3 * (p 2 - 2 * p 1 + p 0) / 2 ^ 2 = (3 / 2) * p 1 at hm
  change p 2 = 0 at h₂
  have h₁ : p 1 = 2 := by linarith
  have hp : p = ![8, 2, 0] := by funext i; fin_cases i <;> assumption
  have hc : cost 2 3 (3 / 2) p = 264 := by rw [hp]; norm_num [cost, Fin.sum_univ_succ]
  refine ⟨p, hp, hc, fun x hx₀ hx₂ => ?_⟩
  rw [← hc]
  exact (hmin x hx₀ hx₂).2

-- Turning off the penalty restores the midpoint rule, with the same nonunit time step.
example : ∃ p : Fin 3 → ℝ, p 0 = 8 ∧ p 1 = 4 ∧ p 2 = 0 ∧
    ∀ x : Fin 3 → ℝ, x 0 = 8 → x 2 = 0 → cost 2 3 0 p ≤ cost 2 3 0 x := by
  obtain ⟨p, h₀, h₂, hmin, he⟩ := exists_unique_optimal_path (N := 2) (Δ := 2) (η := 3)
    (κ := 0) (by decide) (by norm_num) (by norm_num) le_rfl 8
  have hm := he 1 (by decide) (by decide)
  change 3 * (p 2 - 2 * p 1 + p 0) / 2 ^ 2 = 0 * p 1 at hm
  change p 2 = 0 at h₂
  exact ⟨p, h₀, by linarith, h₂, fun x hx₀ hx₂ => (hmin x hx₀ hx₂).1⟩

-- Three intervals exercise both ends of the interior recurrence on the same signed path.
example : ∃ p : Fin 4 → ℝ, p = ![-8, -3, -1, 0] ∧
    ∀ x : Fin 4 → ℝ, x 0 = -8 → x 3 = 0 → cost 1 1 1 p ≤ cost 1 1 1 x := by
  obtain ⟨p, h₀, h₃, hmin, he⟩ := exists_unique_optimal_path (N := 3) (Δ := 1) (η := 1)
    (κ := 1) (by decide) (by norm_num) (by norm_num) (by norm_num) (-8)
  have h₁ := he 1 (by decide) (by decide)
  have h₂ := he 2 (by decide) (by decide)
  change 1 * (p 2 - 2 * p 1 + p 0) / 1 ^ 2 = 1 * p 1 at h₁
  change 1 * (p 3 - 2 * p 2 + p 1) / 1 ^ 2 = 1 * p 2 at h₂
  change p 3 = 0 at h₃
  refine ⟨p, ?_, fun x hx₀ hx₃ => (hmin x hx₀ hx₃).1⟩
  have hm₁ : p 1 = -3 := by linarith
  have hm₂ : p 2 = -1 := by linarith
  funext i; fin_cases i <;> assumption

-- With just one interval, the negative initial inventory incurs the left-endpoint penalty.
example (x : Fin 2 → ℝ) (h₀ : x 0 = -4) (h₁ : x 1 = 0) :
    x = ![-4, 0] ∧ cost 2 3 (3 / 2) x = 72 := by
  have hx : x = ![-4, 0] := by funext i; fin_cases i <;> assumption
  exact ⟨hx, by rw [hx]; norm_num [cost, Fin.sum_univ_succ]⟩
