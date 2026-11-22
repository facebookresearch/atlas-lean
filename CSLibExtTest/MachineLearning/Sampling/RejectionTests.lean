/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.Rejection

@[expose] public section

/-!
# Tests for rejection sampling
-/

set_option autoImplicit false

open Cslib.MachineLearning.Sampling
open scoped ENNReal NNReal

namespace CSLibExtTest.MachineLearning.Sampling.Rejection

/-- A target on `Bool` with `P(true) = 3 / 4`. -/
noncomputable def target : PMF Bool :=
  PMF.ofFintype (fun b ↦ ((cond b (3 / 4) (1 / 4) : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, ← ENNReal.coe_add, ← ENNReal.coe_one,
      ENNReal.coe_inj, ← NNReal.coe_inj]
    push_cast
    norm_num)

/-- The uniform proposal on `Bool`. -/
noncomputable def proposal : PMF Bool :=
  PMF.ofFintype (fun _ ↦ ((1 / 2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj, add_halves])

/-- The envelope `M = 3 / 2` dominates: `target ≤ M · proposal`. -/
theorem envelope (b : Bool) : target b ≤ ((3 / 2 : ℝ≥0) : ℝ≥0∞) * proposal b := by
  simp only [target, proposal, PMF.ofFintype_apply, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe]
  cases b <;> norm_num

/-- A round proposes `true` and accepts it with probability `(3/4) / (3/2) = 1/2`. -/
example : trial target proposal _ envelope (true, true) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [trial_apply_true]
  simp only [target, PMF.ofFintype_apply, Bool.cond_true]
  rw [← ENNReal.coe_div (by norm_num), ENNReal.coe_inj, ← NNReal.coe_inj]
  push_cast
  norm_num

/-- A round accepts with probability `2 / 3`. -/
example : ∑' b, trial target proposal _ envelope (b, true) = ((2 / 3 : ℝ≥0) : ℝ≥0∞) := by
  rw [tsum_trial_true, ← ENNReal.coe_inv (by norm_num), ENNReal.coe_inj, ← NNReal.coe_inj]
  push_cast
  norm_num

/-- The output of the accept–reject loop has the target law. -/
example (b : Bool) :
    ∑' k : ℕ, (∑' y, trial target proposal _ envelope (y, false)) ^ k *
      trial target proposal _ envelope (b, true) = target b :=
  tsum_rejections_mul_trial envelope (by norm_num) ENNReal.coe_ne_top b

end CSLibExtTest.MachineLearning.Sampling.Rejection
