/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.MetropolisHastings

@[expose] public section

/-!
# Tests for Metropolis–Hastings
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.Sampling
open scoped ENNReal NNReal

namespace CSLibExtTest.MachineLearning.Sampling.MetropolisHastings

/-- A target on `Bool` with `π(true) = 3 / 4`. -/
noncomputable def target : PMF Bool :=
  PMF.ofFintype (fun b ↦ ((cond b (3 / 4) (1 / 4) : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, ← ENNReal.coe_add, ← ENNReal.coe_one,
      ENNReal.coe_inj, ← NNReal.coe_inj]
    push_cast
    norm_num)

/-- The proposal that always suggests the other state. -/
noncomputable def flip (b : Bool) : PMF Bool := PMF.pure (!b)

/-- From `true` the flip is accepted with probability `min(1, (1/4) / (3/4)) = 1 / 3`. -/
example : mhStep target flip true false = ((1 / 3 : ℝ≥0) : ℝ≥0∞) := by
  rw [mhStep_apply_of_ne (by decide : true ≠ false), mhAccept]
  simp only [flip, PMF.pure_apply, target, PMF.ofFintype_apply, Bool.not_true, Bool.not_false,
    Bool.cond_true, Bool.cond_false, ite_true, one_mul, mul_one]
  rw [← ENNReal.coe_div (by norm_num), ← ENNReal.coe_one, ← ENNReal.coe_min, ENNReal.coe_inj,
    ← NNReal.coe_inj]
  push_cast
  norm_num

/-- From `false` the flip is always accepted. -/
example : mhStep target flip false true = 1 := by
  rw [mhStep_apply_of_ne (by decide : false ≠ true), mhAccept]
  simp only [flip, PMF.pure_apply, target, PMF.ofFintype_apply, Bool.not_true, Bool.not_false,
    Bool.cond_true, Bool.cond_false, ite_true, one_mul, mul_one]
  rw [min_eq_left]
  rw [← ENNReal.coe_div (by norm_num), ← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast
  norm_num

/-- The target is stationary for the resulting chain. -/
example : target.bind (mhStep target flip) = target := bind_mhStep target flip

example : (pmfKernel (mhStep target flip)).Invariant target.toMeasure :=
  invariant_mhKernel target flip

end CSLibExtTest.MachineLearning.Sampling.MetropolisHastings
