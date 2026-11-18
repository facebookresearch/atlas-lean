/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Comp
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

private theorem anchored_le_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ} {γ : ℝ → E} {f : ℝ → E → E} {a b : ℝ} (hab : a ≤ b)
    (hVγ : ContinuousOn (V ∘ γ) (Set.Icc a b))
    (hγderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (f t (γ t)) t)
    (hVdiff : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ V (γ t))
    (hDV : ∀ t ∈ Set.Ioo a b, fderiv ℝ V (γ t) (f t (γ t)) ≤ 0) :
    ∀ t ∈ Set.Icc a b, V (γ t) ≤ V (γ a) := by
  have hchain : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (V ∘ γ) (fderiv ℝ V (γ x) (f x (γ x))) x := fun x hx =>
    ((hVdiff x hx).hasFDerivAt).comp_hasDerivAt x (hγderiv x hx)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact le_rfl
  · show (V ∘ γ) t ≤ (V ∘ γ) a
    have key : ∀ s ∈ Set.Ioo a t, (V ∘ γ) t ≤ (V ∘ γ) s := by
      intro s hs
      have hmemI : ∀ x ∈ Set.Ico s t, x ∈ Set.Ioo a b := fun x hx =>
        ⟨lt_of_lt_of_le hs.1 hx.1, lt_of_lt_of_le hx.2 ht.2⟩
      have hcont : ContinuousOn (V ∘ γ) (Set.Icc s t) :=
        hVγ.mono (Set.Icc_subset_Icc hs.1.le ht.2)
      have hderiv : ∀ x ∈ Set.Ico s t,
          HasDerivWithinAt (V ∘ γ) (fderiv ℝ V (γ x) (f x (γ x))) (Set.Ici x) x :=
        fun x hx => (hchain x (hmemI x hx)).hasDerivWithinAt
      have hbound : ∀ x ∈ Set.Ico s t, fderiv ℝ V (γ x) (f x (γ x)) ≤ 0 :=
        fun x hx => hDV x (hmemI x hx)
      have hB : ContinuousOn (fun _ => (V ∘ γ) s) (Set.Icc s t) := continuousOn_const
      have hB' : ∀ x ∈ Set.Ico s t,
          HasDerivWithinAt (fun _ => (V ∘ γ) s) 0 (Set.Ici x) x :=
        fun x _ => hasDerivWithinAt_const x (Set.Ici x) _
      have ha : (V ∘ γ) s ≤ (fun _ => (V ∘ γ) s) s := le_rfl
      exact image_le_of_deriv_right_le_deriv_boundary (B := fun _ => (V ∘ γ) s)
        (B' := fun _ => 0) hcont hderiv ha hB hB' hbound ⟨hs.2.le, le_rfl⟩
    have hmem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
    have hcw : ContinuousWithinAt (V ∘ γ) (Set.Icc a b) a := hVγ a hmem
    have hIcc_mem : Set.Icc a b ∈ nhdsWithin a (Set.Ioi a) :=
      Filter.mem_of_superset (Ioo_mem_nhdsGT hat)
        (fun s hs => ⟨hs.1.le, (hs.2.trans_le ht.2).le⟩)
    have hle : nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a (Set.Icc a b) :=
      nhdsWithin_le_of_mem hIcc_mem
    have htend : Filter.Tendsto (V ∘ γ) (nhdsWithin a (Set.Ioi a))
        (nhds ((V ∘ γ) a)) :=
      Filter.Tendsto.mono_left hcw hle
    have hev : Filter.Eventually (fun s => (V ∘ γ) t ≤ (V ∘ γ) s)
        (nhdsWithin a (Set.Ioi a)) := by
      filter_upwards [Ioo_mem_nhdsGT hat] with s hs
      exact key s hs
    exact ge_of_tendsto htend hev

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
    {V : E → ℝ} {γ : ℝ → E} {f : ℝ → E → E} {a b : ℝ} (hab : a ≤ b)
    (hVγ : ContinuousOn (V ∘ γ) (Set.Icc a b))
    (hγderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (f t (γ t)) t)
    (hVdiff : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ V (γ t))
    (hDV : ∀ t ∈ Set.Ioo a b, fderiv ℝ V (γ t) (f t (γ t)) ≤ 0) :
    AntitoneOn (V ∘ γ) (Set.Icc a b) := by
  have _ := hab
  intro x hx y hy hxy
  have hxb : x ≤ b := le_trans hxy hy.2
  have hsub : Set.Icc x b ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 le_rfl
  have hmem : ∀ t ∈ Set.Ioo x b, t ∈ Set.Ioo a b :=
    fun t ht => ⟨lt_of_le_of_lt hx.1 ht.1, ht.2⟩
  exact anchored_le_left hxb (hVγ.mono hsub)
    (fun t ht => hγderiv t (hmem t ht))
    (fun t ht => hVdiff t (hmem t ht))
    (fun t ht => hDV t (hmem t ht))
    y ⟨hxy, hy.2⟩

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
  have hanti := finite_interval_antitoneOn_v_comp hab hVγ hγderiv hVdiff hDV
  intro t ht
  show V (γ t) ≤ c
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  exact le_trans (hanti ha ht ht.1) hinit

end MathlibExt.Analysis.ODE
