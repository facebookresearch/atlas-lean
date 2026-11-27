/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.JensenHyperbolicity
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.IntervalCases

open Filter Polynomial Asymptotics MetaMathlibExt

-- For the constant sequence and degree one, taking A = δ² gives an exact expansion.
example : ∀ᶠ _n : ℕ in atTop, (1 + X : ℝ[X]).roots.card = 1 := by
  let δ (n : ℕ) : ℝ := 1 / (n + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have H := eventually_jensen_hyperbolic_of_log_ratio_expansion
    (α := fun _ => 1) (A := fun n => δ n ^ 2) (δ := δ) (d := 1) (fun _ => zero_lt_one)
    (fun n => sq_pos_of_pos (hδ n)) hδ tendsto_one_div_add_atTop_nhds_zero_nat
    (by decide) (fun _ _ => 0) (by simp) (by
      intro k hk
      interval_cases k <;> simp)
  simpa [Finset.sum_range_succ, natDegree_add_eq_right_of_natDegree_lt] using H

-- In degree two there are no higher-order coefficients. Only the first two shifts matter.
example {α A δ : ℕ → ℝ} (hα : ∀ n, 0 < α n) (hA : ∀ n, 0 < A n) (hδ : ∀ n, 0 < δ n)
    (hδ0 : Tendsto δ atTop (nhds 0))
    (h₁ : (fun n => Real.log (α (n + 1) / α n) - (A n - δ n ^ 2)) =o[atTop]
      fun n => δ n ^ 2)
    (h₂ : (fun n => Real.log (α (n + 2) / α n) - (A n * 2 - δ n ^ 2 * 4)) =o[atTop]
      fun n => δ n ^ 2) :
    ∀ᶠ n in atTop, (C (α (n + 2)) * X ^ 2 + C (2 * α (n + 1)) * X + C (α n)).roots.card = 2 := by
  have H := eventually_jensen_hyperbolic_of_log_ratio_expansion hα hA hδ hδ0
    (d := 2) (by decide) (fun _ _ => 0) (by simp) (by
      intro k hk
      interval_cases k
      · simp [(hα _).ne']
      · simpa using h₁
      · convert h₂ using 1
        norm_num)
  filter_upwards [H] with n hn
  calc
    _ = (C (α (n + 2)) * X ^ 2 + C (2 * α (n + 1)) * X + C (α n)).natDegree := by
      simpa [Finset.sum_range_succ, Nat.choose, map_ofNat, add_comm, add_left_comm, add_assoc]
        using hn
    _ = 2 := natDegree_quadratic (hα _).ne'
