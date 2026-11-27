/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.DirichletPointwise
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

open Filter Topology MathlibExt.Analysis.FourierConvergenceWanted.Analysis

-- The real point 0 lies at the excluded endpoint of the circle lift's representative interval.
example (c : ℂ) :
    Tendsto (fun N : ℕ => fourierPartialSum (fun _ => c) N 0) atTop (𝓝 c) :=
  dirichlet_pointwise (_hperiod := fun _ => rfl) (_hC1 := contDiff_const) 0

-- The negative-frequency character converges at a point below the representative interval.
example :
    Tendsto
      (fun N : ℕ => fourierPartialSum (fun x => Complex.exp (-(x : ℂ) * Complex.I))
        N (-2 * Real.pi)) atTop (𝓝 1) := by
  have hperiod :
      Function.Periodic (fun x : ℝ => Complex.exp (-(x : ℂ) * Complex.I)) (2 * Real.pi) := by
    intro x
    push_cast
    simp only [neg_add, add_mul, Complex.exp_add, neg_mul, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, inv_one, mul_one]
  have hOfReal : ContDiff ℝ 1 ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  have hC1 : ContDiff ℝ 1 (fun x : ℝ => Complex.exp (-(x : ℂ) * Complex.I)) :=
    (hOfReal.neg.mul (contDiff_const (c := Complex.I))).cexp
  simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat, neg_mul, neg_neg,
    Complex.exp_two_pi_mul_I] using
    dirichlet_pointwise hperiod hC1 (-2 * Real.pi)

#print axioms MathlibExt.Analysis.FourierConvergenceWanted.Analysis.dirichlet_pointwise
