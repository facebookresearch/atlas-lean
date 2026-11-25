/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.ReluVCInversion
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tests for BHLM VC inversion

Closed instances of the BHLM shatter-bound inversion: the hypothesis
`2 ≤ p` is necessary (the bare inversion fails at `(p, L) = (1, 9)`),
and the smallest admissible instance `p = 2`, `L = 6` evaluates to
`72 * Real.log 12`.
-/

namespace Cslib.MachineLearning.PACLearning

/-- Necessity of `2 ≤ p`: at `(p, L) = (1, 9)` the bare inversion fails,
witnessed by `n = 123`. -/
theorem bhlm_needs_two_le_p :
    ¬ ∀ n : ℕ, (2 : ℝ) ^ n ≤ (12 * (n : ℝ) * 9) ^ 9 →
      (n : ℝ) ≤ 6 * 9 * Real.log 9 := by
  intro hall
  have hpow : (2 : ℝ) ^ (123 : ℕ) ≤ (12 * ((123 : ℕ) : ℝ) * 9) ^ 9 := by
    norm_num
  have hcon := hall 123 hpow
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hub : (6 : ℝ) * 9 * Real.log 9 < 123 := by
    rw [hlog9]
    have hle : Real.log 3 < (41 / 36 : ℝ) :=
      lt_trans Real.log_three_lt_d9
        (show (1.0986122888 : ℝ) < 41 / 36 by norm_num)
    linarith only [hle]
  push_cast at hcon
  linarith only [hcon, hub]

/-- Smallest admissible instance `p = 2`, `L = 6`: the lemma applies and the
bound evaluates to `72 * Real.log 12`. -/
theorem bhlm_smallest_admissible (n : ℕ)
    (h : (2 : ℝ) ^ n ≤ (12 * (n : ℝ) * 6) ^ (2 * 6)) :
    (n : ℝ) ≤ 72 * Real.log 12 := by
  have hcast : ((6 : ℕ) : ℝ) = 6 := by norm_num
  have h' : (2 : ℝ) ^ n ≤ (12 * (n : ℝ) * ((6 : ℕ) : ℝ)) ^ (2 * 6) := by
    rw [hcast]
    exact h
  have hle :=
    le_six_mul_log_of_two_pow_le_bhlm 2 6 n (by norm_num) (by norm_num) h'
  have e1 : ((2 * 6 : ℕ) : ℝ) = 12 := by norm_num
  rw [e1] at hle
  have heq : (6 : ℝ) * 12 * Real.log 12 = 72 * Real.log 12 := by ring
  rw [heq] at hle
  exact hle

/-- The `n = 1` instance of the smallest admissible case, with a checked
hypothesis. -/
theorem bhlm_instance_one_le : ((1 : ℕ) : ℝ) ≤ 72 * Real.log 12 := by
  have h1 : (2 : ℝ) ^ (1 : ℕ) ≤ (12 * (((1 : ℕ)) : ℝ) * 6) ^ (2 * 6) := by
    norm_num
  exact bhlm_smallest_admissible 1 h1

#print axioms le_six_mul_log_of_two_pow_le_bhlm
#print axioms vcDim_le_of_growthFunction_le_bhlm

end Cslib.MachineLearning.PACLearning
