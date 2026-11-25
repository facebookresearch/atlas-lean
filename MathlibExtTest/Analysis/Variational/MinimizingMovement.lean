/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Variational.MinimizingMovement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

open Finset MathlibExt.Analysis.Variational.MinimizingMovement

namespace MathlibExtTest.Analysis.Variational.MinimizingMovement

/-- Non-vacuity: for the quadratic energy `F z = λ z² / 2` on `ℝ` (`λ ≥ 0`, `h > 0`) the JKO step
from `x` is the implicit Euler step `x / (1 + hλ)` of the gradient flow `ẋ = -λ x`. -/
theorem isMinimizingMovementStep_quadratic {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) (x : ℝ) :
    IsMinimizingMovementStep (fun z : ℝ => lam * z ^ 2 / 2) h x (x / (1 + h * lam)) := by
  intro z
  have hpos : 0 < 1 + h * lam := by positivity
  rw [Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  set y := x / (1 + h * lam) with hy
  have hyx : x = (1 + h * lam) * y := by rw [hy]; field_simp
  rw [hyx]
  nlinarith [sq_nonneg (z - y), mul_nonneg hh.le hlam]

/-- The discrete trajectory `ρₖ = x / (1 + hλ)ᵏ` solves the JKO scheme for the quadratic energy. -/
theorem isMinimizingMovement_quadratic {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) (x : ℝ) :
    IsMinimizingMovement (fun z : ℝ => lam * z ^ 2 / 2) h (fun k => x / (1 + h * lam) ^ k) := by
  intro k
  have := isMinimizingMovementStep_quadratic hlam hh (x / (1 + h * lam) ^ k)
  simpa [pow_succ, div_div] using this

/-- The energy decreases along that trajectory (an instance of `IsMinimizingMovement.antitone`). -/
example {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) (x : ℝ) :
    Antitone (fun k : ℕ => lam * (x / (1 + h * lam) ^ k) ^ 2 / 2) :=
  (isMinimizingMovement_quadratic hlam hh x).antitone hh

/-- The discrete energy inequality on that trajectory, for `N = 3` steps. -/
example {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) (x : ℝ) :
    (∑ k ∈ range 3, dist (x / (1 + h * lam) ^ k) (x / (1 + h * lam) ^ (k + 1)) ^ 2) / (2 * h) +
        lam * (x / (1 + h * lam) ^ 3) ^ 2 / 2 ≤ lam * (x / (1 + h * lam) ^ 0) ^ 2 / 2 :=
  (isMinimizingMovement_quadratic hlam hh x).energy_sum_le hh 3

/-- Existence on `ℝ` (a proper space) for a continuous energy bounded below. -/
example (h : ℝ) (hh : 0 < h) (x₀ : ℝ) :
    ∃ ρ : ℕ → ℝ, ρ 0 = x₀ ∧ IsMinimizingMovement (fun z : ℝ => |z|) h ρ :=
  exists_isMinimizingMovement continuous_abs.lowerSemicontinuous ⟨0, by
    rintro _ ⟨z, rfl⟩; exact abs_nonneg z⟩ hh x₀

end MathlibExtTest.Analysis.Variational.MinimizingMovement
