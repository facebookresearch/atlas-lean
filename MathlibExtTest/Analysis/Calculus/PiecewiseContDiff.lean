/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.PiecewiseContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open Set MathlibExt.Analysis.Calculus.PiecewiseContDiffWanted

-- The two distinct branches match in value and first derivative at zero.
example : ContDiffOn ℝ 1 ((Icc (-1 : ℝ) 0).piecewise (fun _ ↦ 0) (fun x ↦ x ^ 2))
    (Icc (-1 : ℝ) 1) := by
  have hf : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
  have hg : ContDiff ℝ 1 (fun x : ℝ ↦ x ^ 2) := by fun_prop
  refine contDiffOn_piecewise_Icc (n := 1) (by norm_num) (by norm_num)
    hf.contDiffOn hg.contDiffOn ?_
  intro k hk
  have hk' : k ≤ 1 := by exact_mod_cast hk
  interval_cases k
  · simp
  · have hs : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 0 :=
      uniqueDiffOn_Icc (by norm_num) 0 (by norm_num)
    have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2) 0 0 := by
      simpa using hasDerivAt_pow 2 (0 : ℝ)
    rw [show (1 : ℕ) = 0 + 1 from rfl, iteratedDerivWithin_succ,
      iteratedDerivWithin_succ, iteratedDerivWithin_zero, iteratedDerivWithin_zero]
    simp [hsq.hasDerivWithinAt.derivWithin hs]
