/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.RolewiczPeriodic

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Tests for dense periodic points of the Rolewicz backward shift

* The geometric vector `(1/2)^n` is a fixed point of `2 • B`.
* `periodicApprox 2 3 y` is periodic of period `3`.
* A periodic point of `2 • B` approximates `e₀` within `1/2`.
* No nonzero periodic point of `1 • B`.
* The dichotomy: periodic points of `2 • B` are dense, those of `1 • B`
  are not.
* `#print axioms` for the dichotomy: standard triple only.
-/

open Set Filter Topology Metric
open scoped _root_.lp ENNReal
open MathlibExt.Analysis.FunctionalAnalysis.RolewiczPeriodic

namespace MathlibExtTest.Analysis.FunctionalAnalysis.RolewiczPeriodicTests

/-- The geometric vector with coordinates `(1/2)^n` in `ℓ²(ℕ, ℂ)`. -/
noncomputable def geometric : ℓ²(ℕ, ℂ) :=
  ⟨fun n => (((1 / 2 : ℝ) ^ n : ℝ) : ℂ), by
    apply memℓp_gen
    have h : Summable (fun n : ℕ => ((1 : ℝ) / 4) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine h.congr (fun n => ?_)
    have hnorm : ‖(((1 / 2 : ℝ) ^ n : ℝ) : ℂ)‖ = (1 / 2 : ℝ) ^ n := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n by positivity)]
    rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by simp, hnorm, Real.rpow_two,
      show ((1 : ℝ) / 4) = (1 / 2 : ℝ) ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm n 2]⟩

/-- The geometric vector is a fixed point of `2 • B`. -/
example : IsPeriodicPoint ((2 : ℂ) • backwardShiftCLM) 1 geometric := by
  show (((2 : ℂ) • backwardShiftCLM) ^ 1) geometric = geometric
  apply lp.ext
  funext k
  rw [smul_backwardShiftCLM_pow_apply_coord, pow_one]
  show (2 : ℂ) * (((1 / 2 : ℝ) ^ (k + 1) : ℝ) : ℂ) = (((1 / 2 : ℝ) ^ k : ℝ) : ℂ)
  rw [pow_succ]
  push_cast
  ring

/-- `periodicApprox 2 3 y` is periodic of period `3`. -/
example (y : ℓ²(ℕ, ℂ)) :
    IsPeriodicPoint ((2 : ℂ) • backwardShiftCLM) 3 (periodicApprox (2 : ℂ) 3 y) :=
  periodicApprox_isPeriodicPoint (by rw [Complex.norm_two]; norm_num) (by norm_num) y

/-- A periodic point of `2 • B` approximates `e₀` within `1/2`. -/
example : ∃ x : ℓ²(ℕ, ℂ),
    (∃ n, 0 < n ∧ IsPeriodicPoint ((2 : ℂ) • backwardShiftCLM) n x) ∧
      dist (lp.single 2 0 (1 : ℂ) : ℓ²(ℕ, ℂ)) x < 1 / 2 := by
  have hdense := dense_periodicPoints_of_one_lt_norm (μ := (2 : ℂ))
    (by rw [Complex.norm_two]; norm_num)
  have hmem : (lp.single 2 0 (1 : ℂ) : ℓ²(ℕ, ℂ)) ∈
      closure {x : ℓ²(ℕ, ℂ) | ∃ n, 0 < n ∧ IsPeriodicPoint ((2 : ℂ) • backwardShiftCLM) n x} := by
    have hc := hdense.closure_eq
    rw [hc]
    exact Set.mem_univ _
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨x, hx, hdist⟩ := hmem (1 / 2) (by norm_num)
  exact ⟨x, hx, hdist⟩

/-- No nonzero periodic point of `1 • B`. -/
example (x : ℓ²(ℕ, ℂ)) (hx : IsPeriodicPoint ((1 : ℂ) • backwardShiftCLM) 3 x) : x = 0 :=
  eq_zero_of_isPeriodicPoint_of_norm_le_one (by simp) (by norm_num) hx

/-- The periodic points of `2 • B` are dense. -/
example : Dense {x : ℓ²(ℕ, ℂ) | ∃ n, 0 < n ∧ IsPeriodicPoint ((2 : ℂ) • backwardShiftCLM) n x} :=
  (dense_periodicPoints_iff (2 : ℂ)).mpr (by rw [Complex.norm_two]; norm_num)

/-- The periodic points of `1 • B` are not dense. -/
example : ¬ Dense {x : ℓ²(ℕ, ℂ) | ∃ n, 0 < n ∧ IsPeriodicPoint ((1 : ℂ) • backwardShiftCLM) n x} := by
  rw [dense_periodicPoints_iff]
  simp

#print axioms MathlibExt.Analysis.FunctionalAnalysis.RolewiczPeriodic.dense_periodicPoints_iff

end MathlibExtTest.Analysis.FunctionalAnalysis.RolewiczPeriodicTests
