/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.Elasticity

/-!
# Tests for point elasticity

Linear demand `10 - 2 p` at `p = 2` has elasticity `-2/3`; constant-elasticity demand `8 / p²`
has elasticity `-2`; and the log-log derivative theorem is instantiated for the linear demand.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Consumer.Elasticity

open MathlibExt.Economics.Consumer

example : pointElasticity (fun p : ℝ => 10 - 2 * p) 2 = -2 / 3 := by
  have h1 : HasDerivAt (fun p : ℝ => (2 : ℝ) * p) 2 2 := by
    simpa using (hasDerivAt_id (2 : ℝ)).const_mul (2 : ℝ)
  have h : HasDerivAt (fun p : ℝ => 10 - 2 * p) (-2 : ℝ) 2 :=
    h1.const_sub (10 : ℝ)
  rw [pointElasticity_eq_of_hasDerivAt h]
  norm_num

example : pointElasticity (fun p : ℝ => 8 / p ^ 2) 2 = -2 := by
  have hpow : HasDerivAt (fun p : ℝ => p ^ 2) (4 : ℝ) 2 := by
    have h := hasDerivAt_pow 2 (2 : ℝ)
    norm_num at h
    exact h
  have h8 : HasDerivAt (fun _ : ℝ => (8 : ℝ)) 0 2 := hasDerivAt_const 2 8
  have h : HasDerivAt (fun p : ℝ => 8 / p ^ 2) (-2 : ℝ) 2 := by
    have h := h8.div hpow (by norm_num)
    norm_num at h
    exact h
  rw [pointElasticity_eq_of_hasDerivAt h]
  norm_num

example : HasDerivAt (fun s => Real.log ((fun p : ℝ => 10 - 2 * p) (Real.exp s)))
    (pointElasticity (fun p : ℝ => 10 - 2 * p) 2) (Real.log 2) := by
  have h1 : HasDerivAt (fun p : ℝ => (2 : ℝ) * p) 2 2 := by
    simpa using (hasDerivAt_id (2 : ℝ)).const_mul (2 : ℝ)
  have h : HasDerivAt (fun p : ℝ => 10 - 2 * p) (-2 : ℝ) 2 :=
    h1.const_sub (10 : ℝ)
  exact hasDerivAt_log_comp_exp_pointElasticity (by norm_num) (by norm_num) h

end MathlibExtTest.Economics.Consumer.Elasticity
