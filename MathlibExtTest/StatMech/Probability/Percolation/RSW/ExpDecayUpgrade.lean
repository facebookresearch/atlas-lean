/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.ExpDecayUpgrade
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.ExpDecayUpgrade`

* `rxd_submul_pow` and `rxd_submultiplicative_forces_exp_decay` for `a n = (1/2)^n`.
* `rxd_exp_decay_of_stretched` and `rxd_exp_decay_literal` for `a n = exp (-n)` with `α = 1`.
-/

@[expose] public section

open StatMech.RSW.ExpDecay

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.ExpDecayUpgrade

theorem halfPow_submult (m n : ℕ) : ((1 / 2 : ℝ) ^ (m + n)) ≤ (1 / 2) ^ m * (1 / 2) ^ n := by
  rw [pow_add]

theorem halfPow_antitone : Antitone (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
  fun _ _ h => pow_le_pow_of_le_one (by norm_num) (by norm_num) h

example (k : ℕ) : (1 / 2 : ℝ) ^ (k * 3) ≤ ((1 / 2 : ℝ) ^ 3) ^ k :=
  rxd_submul_pow (fun n => (1 / 2 : ℝ) ^ n) (fun _ => by positivity) (by norm_num)
    halfPow_submult 3 k

example : ∃ c > 0, ∃ C > 0, ∀ n : ℕ, (1 / 2 : ℝ) ^ n ≤ C * Real.exp (-c * n) :=
  rxd_submultiplicative_forces_exp_decay (fun n => (1 / 2 : ℝ) ^ n) (fun _ => by positivity)
    (fun _ => pow_le_one₀ (by norm_num) (by norm_num)) halfPow_antitone halfPow_submult 1
    one_pos (by norm_num)

theorem expNeg_stretched (n : ℕ) :
    Real.exp (-(n : ℝ)) ≤ Real.exp (-(((n : ℕ) : ℝ) ^ (1 : ℝ))) := by
  simp

example : ∃ c > 0, ∃ C > 0, ∀ n : ℕ, Real.exp (-(n : ℝ)) ≤ C * Real.exp (-c * n) :=
  rxd_exp_decay_of_stretched (fun n : ℕ => Real.exp (-(n : ℝ))) (fun _ => (Real.exp_pos _).le)
    (fun n => Real.exp_le_one_iff.mpr (by simp))
    (fun m n hmn => Real.exp_le_exp.mpr (by simpa using hmn)) 1 one_pos expNeg_stretched
    (fun m n => by rw [← Real.exp_add]; push_cast; ring_nf; exact le_rfl)

example : ∃ c > 0, ∀ n : ℕ, Real.exp (-(n : ℝ)) ≤ Real.exp (-c * n) :=
  rxd_exp_decay_literal (fun n : ℕ => Real.exp (-(n : ℝ))) 1 le_rfl expNeg_stretched

end MathlibExtTest.StatMech.Probability.Percolation.RSW.ExpDecayUpgrade
