/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlzerRichardsBernoulliDerivatives
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- The hypotheses have a witness: `(1 - e^x)/x` extended by `-1` at `0`. Since `B_1 = -1/2`,
-- the first derivative of `x / (1 - e^x)` at `0` is `1/2`.
example :
    deriv (fun x : ℝ => 1 / (if x = 0 then -1 else (1 - Real.exp x) / x)) 0 = 1 / 2 := by
  have h := iteratedDeriv_inv_one_sub_exp_div_self_zero
    (f := fun x : ℝ => if x = 0 then -1 else (1 - Real.exp x) / x) (by simp)
    (fun x hx => by simp [hx]) 1
  rw [iteratedDeriv_one, bernoulli_one] at h
  rw [h]
  norm_num

-- At order `0` the theorem agrees with the value `1 / f 0 = -1 = -B_0`.
example {f : ℝ → ℝ} (hf0 : f 0 = -1) (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) :
    iteratedDeriv 0 (fun x => 1 / f x) 0 = 1 / f 0 := by
  rw [iteratedDeriv_inv_one_sub_exp_div_self_zero hf0 hf 0, bernoulli_zero, hf0]
  norm_num

-- The second derivative is `-B_2 = -1/6`.
example {f : ℝ → ℝ} (hf0 : f 0 = -1) (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) :
    iteratedDeriv 2 (fun x => 1 / f x) 0 = -1 / 6 := by
  rw [iteratedDeriv_inv_one_sub_exp_div_self_zero hf0 hf 2, bernoulli_two]
  norm_num

-- The odd derivatives of order at least `3` vanish.
example {f : ℝ → ℝ} (hf0 : f 0 = -1) (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) (n : ℕ) :
    iteratedDeriv (2 * n + 3) (fun x => 1 / f x) 0 = 0 := by
  rw [iteratedDeriv_inv_one_sub_exp_div_self_zero hf0 hf,
    bernoulli_eq_zero_of_odd ⟨n + 1, by ring⟩ (by omega)]
  simp
