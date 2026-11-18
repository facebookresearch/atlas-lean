/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Forward uniqueness for autonomous fields

Two forward solutions of the same autonomous field with a global
Lipschitz constant, starting at the same initial value, agree on
every common forward interval and hence at its endpoint.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MathlibExt.Analysis.ODE.FiniteBoxFlowUniqueness

/-- **Forward uniqueness on a common interval.** Two forward
solutions of the same autonomous field `F` with a global
Lipschitz constant, starting at the same initial value at time
`0`, agree on every common forward interval `[0, T]`. -/
theorem forward_unique_eqOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F)
    {T : ℝ} {x y : ℝ → E} (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hx' : ∀ t ∈ Ico (0:ℝ) T, HasDerivWithinAt x (F (x t)) (Ici t) t)
    (hy' : ∀ t ∈ Ico (0:ℝ) T, HasDerivWithinAt y (F (y t)) (Ici t) t)
    (h0 : x 0 = y 0) :
    EqOn x y (Icc 0 T) := by
  exact ODE_solution_unique (fun _ => hF) hx hx' hy hy' h0

/-- **Forward uniqueness at a later time.** Under the same
hypotheses the two solutions agree at the endpoint `T`. -/
theorem forward_unique_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F)
    {T : ℝ} {x y : ℝ → E} (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hx' : ∀ t ∈ Ico (0:ℝ) T, HasDerivWithinAt x (F (x t)) (Ici t) t)
    (hy' : ∀ t ∈ Ico (0:ℝ) T, HasDerivWithinAt y (F (y t)) (Ici t) t)
    (h0 : x 0 = y 0) (hT : 0 ≤ T) :
    x T = y T := by
  exact forward_unique_eqOn hF hx hy hx' hy' h0 (right_mem_Icc.mpr hT)


end MathlibExt.Analysis.ODE.FiniteBoxFlowUniqueness
