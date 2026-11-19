/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.GovernmentDebtConvergence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for constant-deficit debt-ratio convergence

The affine recursion `b t = 2 - 2 * (1/2)^t` converges to `2`, and a
concrete debt-ratio instance with `r = 0`, `g = 1`, deficit ratio `1`
converges to `2`.
-/

@[expose] public section

open Filter Topology

namespace MathlibExtTest.Economics.Macro.GovernmentDebtConvergence

open MathlibExt.Economics.Macro.GovernmentDebtConvergence

theorem test_affine_half :
    Tendsto (fun t : ℕ => 2 - 2 * (1 / 2 : ℝ) ^ t) atTop (𝓝 2) := by
  have ha : |(1 / 2 : ℝ)| < 1 := by norm_num
  have hb : ∀ t : ℕ, 2 - 2 * (1 / 2 : ℝ) ^ (t + 1)
      = (1 / 2) * (2 - 2 * (1 / 2 : ℝ) ^ t) + 1 := by
    intro t
    rw [pow_succ]
    ring
  have h := affineRecurrence_tendsto (a := (1 / 2 : ℝ)) (d := (1 : ℝ))
    (b := fun t : ℕ => 2 - 2 * (1 / 2 : ℝ) ^ t) ha hb
  have hval : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
  rw [hval] at h
  exact h

theorem test_debtRatio_half :
    Tendsto (debtRatio (fun t : ℕ => (2 : ℝ) ^ (t + 1) - 2)
      (fun t : ℕ => (2 : ℝ) ^ t)) atTop (𝓝 2) := by
  have hg : (1 : ℝ) + 1 ≠ 0 := by norm_num
  have hY : ∀ t : ℕ, (2 : ℝ) ^ t ≠ 0 := by
    intro t
    positivity
  have hYg : ∀ t : ℕ, (2 : ℝ) ^ (t + 1) = (1 + 1) * (2 : ℝ) ^ t := by
    intro t
    rw [pow_succ]
    ring
  have hB : ∀ t : ℕ, (2 : ℝ) ^ (t + 1 + 1) - 2
      = (1 + 0) * ((2 : ℝ) ^ (t + 1) - 2) + (2 : ℝ) ^ (t + 1) := by
    intro t
    rw [pow_succ]
    ring
  have hD : ∀ t : ℕ, deficitRatio (fun s : ℕ => (2 : ℝ) ^ s)
      (fun s : ℕ => (2 : ℝ) ^ s) (t + 1) = 1 := by
    intro t
    simp only [deficitRatio]
    exact div_self (by positivity)
  have hstable : |(1 + (0 : ℝ)) / (1 + (1 : ℝ))| < 1 := by norm_num
  have h := debtRatio_tendsto_of_stable (r := (0 : ℝ)) (g := (1 : ℝ)) (d := (1 : ℝ))
    (B := fun t : ℕ => (2 : ℝ) ^ (t + 1) - 2) (D := fun t : ℕ => (2 : ℝ) ^ t)
    (Y := fun t : ℕ => (2 : ℝ) ^ t) hg hY hYg hB hD hstable
  have hval : (1 : ℝ) / (1 - (1 + 0) / (1 + 1)) = 2 := by norm_num
  rw [hval] at h
  exact h

end MathlibExtTest.Economics.Macro.GovernmentDebtConvergence
