/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The softplus function

`Real.softplus x = log (1 + exp x)`. Its derivative is the logistic function `Real.sigmoid`
(`Real.hasDerivAt_softplus`), and since `Real.sigmoid` is monotone, softplus is convex on `ℝ`
(`Real.convexOn_softplus`).
-/

@[expose] public section

open Set

namespace Real

/-- The softplus function `x ↦ log (1 + exp x)`. -/
noncomputable def softplus (x : ℝ) : ℝ := log (1 + exp x)

/-- The derivative of softplus is the logistic function `sigmoid`. -/
theorem hasDerivAt_softplus (x : ℝ) : HasDerivAt softplus (sigmoid x) x := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + exp t) (exp x) x := (hasDerivAt_exp x).const_add 1
  have h2 : HasDerivAt (fun t : ℝ => log (1 + exp t)) (exp x / (1 + exp x)) x :=
    h1.log (by positivity)
  have h3 : exp x / (1 + exp x) = sigmoid x := by
    rw [sigmoid_def, exp_neg]
    have hexp : exp x ≠ 0 := exp_ne_zero x
    have hne : (1 : ℝ) + (exp x)⁻¹ ≠ 0 := by positivity
    field_simp
    ring
  rw [h3] at h2
  exact h2

/-- Softplus is convex on `ℝ`: its derivative `sigmoid` is monotone. -/
theorem convexOn_softplus : ConvexOn ℝ univ softplus := by
  have hderiv : deriv softplus = sigmoid := funext fun x => (hasDerivAt_softplus x).deriv
  refine MonotoneOn.convexOn_of_deriv convex_univ ?_ ?_ ?_
  · exact fun x _ => (hasDerivAt_softplus x).continuousAt.continuousWithinAt
  · rw [interior_univ]
    exact fun x _ => (hasDerivAt_softplus x).differentiableAt.differentiableWithinAt
  · rw [interior_univ, hderiv]
    exact sigmoid_monotone.monotoneOn _

end Real
