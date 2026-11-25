/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.TaylorLittleoRemainder
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

open MathlibExt.Analysis.Calculus.TaylorLittleoRemainderWanted
open scoped Topology Asymptotics

-- The degree-one polynomial of `xy` at `(2, 3)` leaves exactly the mixed quadratic term.
example : (fun x : ℝ × ℝ ↦ (x.1 - 2) * (x.2 - 3)) =o[𝓝 ((2, 3) : ℝ × ℝ)]
    fun x ↦ ‖x - ((2, 3) : ℝ × ℝ)‖ := by
  let a : ℝ × ℝ := (2, 3)
  let f (x : ℝ × ℝ) : ℝ := x.1 * x.2
  have hf : ContDiffAt ℝ 1 f a := by fun_prop
  have hfst : HasFDerivAt (@Prod.fst ℝ ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) a := hasFDerivAt_fst
  have hsnd : HasFDerivAt (@Prod.snd ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) a := hasFDerivAt_snd
  have hd : fderiv ℝ f a = (2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ +
      (3 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ := (hfst.mul hsnd).fderiv
  have h := taylor_isLittleO_multivariable (n := 1) hf
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, hd, pow_one] at h
  refine h.congr_left fun x ↦ ?_
  simp [f, a]
  ring
