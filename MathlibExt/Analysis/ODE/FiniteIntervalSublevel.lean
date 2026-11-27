/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Basic.Real.Basic

/-!
# Finite-interval sublevel invariance

Along one path `γ` on a finite interval `[a, b]`, if the
orbital derivative of `V` is nonpositive at every interior
point, then `V ∘ γ` is antitone on `[a, b]`: `V` does not
increase along the path. Hence an initial sublevel bound
`V (γ a) ≤ c` persists on the whole interval, stated as
`Set.MapsTo γ (Set.Icc a b) {x | V x ≤ c}`, with no global
extension of the path.
-/

@[expose] public section

namespace MathlibExt.Analysis.ODE

/-- Finite-interval monotonicity along one path. Let `γ`
be a path into a normed space `E`, with `V ∘ γ` continuous
on `[a, b]`, and suppose that at every interior point `t`
the path has derivative `f t (γ t)`, `V` is differentiable
at `γ t`, and the orbital derivative satisfies
`fderiv ℝ V (γ t) (f t (γ t)) ≤ 0`. Then `V ∘ γ` is
antitone on `[a, b]`: `V` does not increase along the path.
No global extension of the path is used. -/
theorem finite_interval_antitoneOn_v_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ} {γ : ℝ → E} {f : ℝ → E → E} {a b : ℝ}
    (hVγ : ContinuousOn (V ∘ γ) (Set.Icc a b))
    (hγderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (f t (γ t)) t)
    (hVdiff : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ V (γ t))
    (hDV : ∀ t ∈ Set.Ioo a b, fderiv ℝ V (γ t) (f t (γ t)) ≤ 0) :
    AntitoneOn (V ∘ γ) (Set.Icc a b) := by
  have hchain : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (V ∘ γ) (fderiv ℝ V (γ x) (f x (γ x))) x := fun x hx =>
    ((hVdiff x hx).hasFDerivAt).comp_hasDerivAt x (hγderiv x hx)
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hVγ ?_ ?_
  · rw [interior_Icc]
    exact fun x hx => (hchain x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [(hchain x hx).deriv]
    exact hDV x hx

/-- Finite-interval sublevel invariance: under the same
hypotheses, an initial bound `V (γ a) ≤ c` persists along
the whole interval, stated as a set map
`Set.MapsTo γ (Set.Icc a b) {x | V x ≤ c}`. -/
theorem finite_interval_mapsTo_sublevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ} {γ : ℝ → E} {f : ℝ → E → E} {a b : ℝ} (hab : a ≤ b)
    (hVγ : ContinuousOn (V ∘ γ) (Set.Icc a b))
    (hγderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (f t (γ t)) t)
    (hVdiff : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ V (γ t))
    (hDV : ∀ t ∈ Set.Ioo a b, fderiv ℝ V (γ t) (f t (γ t)) ≤ 0)
    {c : ℝ} (hinit : V (γ a) ≤ c) :
    Set.MapsTo γ (Set.Icc a b) {x | V x ≤ c} := by
  have hanti := finite_interval_antitoneOn_v_comp hVγ hγderiv hVdiff hDV
  intro t ht
  show V (γ t) ≤ c
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  exact le_trans (hanti ha ht ht.1) hinit

end MathlibExt.Analysis.ODE
