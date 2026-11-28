/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Height.SchurSiegelSmyth.SchurLowerBound

/-!
# Tests for Schur's lower bound
-/

open MathlibExt.NumberTheory.SchurSiegelSmyth

example : ((Real.sqrt (Real.exp 1) : ℝ) : EReal) ≤ schurSiegelSmythConstant :=
  schur1918LowerBound_wanted

/-- Schur's bound strictly improves the elementary bound of one. -/
example : (1 : EReal) < schurSiegelSmythConstant := by
  have h : (1 : ℝ) < Real.sqrt (Real.exp 1) := by
    rw [Real.lt_sqrt (by norm_num), one_pow]
    exact Real.one_lt_exp_iff.mpr zero_lt_one
  have hcoe := EReal.coe_lt_coe h
  exact (by simpa using hcoe :
    (1 : EReal) < (Real.sqrt (Real.exp 1) : ℝ)).trans_le schur1918LowerBound_wanted
