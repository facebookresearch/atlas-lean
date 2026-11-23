/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BranchingProcess.LinearBirthDeath

import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

open Real Filter Topology Set MathlibExt.Probability.LinearBirthDeath

namespace MathlibExtTest.Probability.BranchingProcess.LinearBirthDeath

/-! ### Initial condition -/

/-- At time `0` the population is one individual. -/
example (b d : ℝ) : prob b d 0 1 = 1 := by simp [prob_zero_time]
example (b d : ℝ) : prob b d 0 0 = 0 := by simp [prob_zero_time]
example (b d : ℝ) : prob b d 0 5 = 0 := by simp [prob_zero_time]

/-! ### Special cases of the closed form -/

/-- Pure birth (Yule process, `d = 0`): extinction is impossible. -/
example (b t : ℝ) : extinctionProb b 0 t = 0 := by
  unfold extinctionProb
  split_ifs <;> simp_all

/-- Pure death (`b = 0`, `d > 0`): the single individual is dead by time `t` with probability
`1 - exp (-d t)`. -/
example (d t : ℝ) (hd : 0 < d) : extinctionProb 0 d t = 1 - exp (-(d * t)) := by
  have := hd.ne'
  simp only [extinctionProb, hd.ne, ↓reduceIte, zero_sub, zero_mul, neg_mul]
  field_simp
  ring

/-- Critical case `b = d = 1` at `t = 1`: `α = 1 / 2`. -/
example : extinctionProb 1 1 1 = 1 / 2 := by norm_num [extinctionProb]

/-- Boundary case `b = d = 0`: nothing happens, so `α t = 0` for all `t`; this is why
`tendsto_extinctionProb_of_le` needs `0 < d`. -/
example (t : ℝ) : extinctionProb 0 0 t = 0 := by simp [extinctionProb]

/-- Junk value outside the domain `t ≥ 0`: for `b = 2`, `d = 1` the denominator `2 E - 1`
vanishes at `t = -log 2`, and the total division returns `0`. -/
example : extinctionProb 2 1 (-Real.log 2) = 0 := by
  have h : exp ((2 - 1) * -Real.log 2) = 2⁻¹ := by
    rw [show (2 - 1 : ℝ) * -Real.log 2 = -Real.log 2 by ring, exp_neg, exp_log two_pos]
  simp only [extinctionProb, show (2 : ℝ) ≠ 1 by norm_num, ↓reduceIte, h]
  norm_num

/-! ### Distribution, mean, Kolmogorov equations -/

/-- The critical process has constant mean `1`. -/
example (b t : ℝ) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    HasSum (fun n : ℕ ↦ (n : ℝ) * prob b b t n) 1 := by
  simpa using hasSum_mul_prob hb hb ht

/-- A concrete supercritical case: mean `exp t` for `b = 2`, `d = 1`. -/
example (t : ℝ) (ht : 0 ≤ t) : HasSum (fun n : ℕ ↦ (n : ℝ) * prob 2 1 t n) (exp t) := by
  convert hasSum_mul_prob (b := 2) (d := 1) (by norm_num) (by norm_num) ht using 2
  norm_num

example (t : ℝ) (ht : 0 ≤ t) : HasSum (prob 2 1 t) 1 := hasSum_prob (by norm_num) (by norm_num) ht

example (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : 0 ≤ prob 1 3 t n :=
  prob_nonneg (by norm_num) (by norm_num) ht n

/-- Forward equation for state `1` in the critical case `b = d = 1`. -/
example (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s ↦ prob 1 1 s 1) (- 2 * prob 1 1 t 1 + 2 * prob 1 1 t 2) t := by
  have := hasDerivAt_prob_succ (b := 1) (d := 1) (by norm_num) (by norm_num) ht 0
  convert this using 1
  push_cast
  ring

/-! ### Extinction probability: backward equation and limits -/

/-- Supercritical limit: `b = 2`, `d = 1` gives `α t → 1 / 2`. -/
example : Tendsto (extinctionProb 2 1) atTop (𝓝 (1 / 2)) :=
  tendsto_extinctionProb_of_lt (by norm_num) (by norm_num)

/-- Critical limit: `b = d = 1` gives certain extinction. -/
example : Tendsto (extinctionProb 1 1) atTop (𝓝 1) :=
  tendsto_extinctionProb_of_le (by norm_num) le_rfl

/-- Subcritical limit. -/
example : Tendsto (extinctionProb 1 2) atTop (𝓝 1) :=
  tendsto_extinctionProb_of_le (by norm_num) (by norm_num)

/-- The extinction probability itself satisfies the hypotheses of the uniqueness theorem. -/
example (b d t : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    HasDerivAt (extinctionProb b d)
      (d - (b + d) * extinctionProb b d t + b * extinctionProb b d t ^ 2) t :=
  hasDerivAt_extinctionProb hb hd ht

end MathlibExtTest.Probability.BranchingProcess.LinearBirthDeath
