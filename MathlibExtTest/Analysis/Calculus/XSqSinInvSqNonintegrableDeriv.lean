/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.XSqSinInvSqNonintegrableDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MeasureTheory Set
open MathlibExt.Analysis.Calculus.XSqSinInvSqNonintegrableDerivWanted

example : DifferentiableAt ℝ (fun x : ℝ => x ^ 2 * Real.sin (1 / x ^ 2)) 0 ∧
    ¬ IntegrableOn (fun x : ℝ => deriv (fun y : ℝ => y ^ 2 * Real.sin (1 / y ^ 2)) x)
      (Icc (-1 : ℝ) 1) := by
  have h := differentiable_and_not_integrableOn_deriv_sq_mul_sin_inv_sq
    (fun x => x ^ 2 * Real.sin (1 / x ^ 2)) (by simp) (fun _ _ => rfl)
  exact ⟨h.1 0, h.2⟩
