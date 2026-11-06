/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.RectangleArgumentPrinciple

/-!
# Tests for the argument principle on a rectangle
-/

open Complex

@[expose] public section

example : ContinuousAt (logDeriv Complex.exp) 0 :=
  (analyticAt_cexp).continuousAt_logDeriv (Complex.exp_ne_zero 0)

/-- A function without zeros: the boundary integral of `E'/E` vanishes. -/
example (r : RectilinearRectangle) :
    r.boundaryIntegral (logDeriv Complex.exp) = 0 := by
  have := r.boundaryIntegral_logDeriv_eq differentiable_exp ∅ (by simp)
    (fun s _ h => absurd h (Complex.exp_ne_zero s))
    (fun p => by
      rw [analyticAt_cexp.analyticOrderAt_eq_zero.2 (Complex.exp_ne_zero p)]
      simp)
  simpa using this
