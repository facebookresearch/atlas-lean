/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerTensorCardinality
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementCardinality
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementPreservation
import MathlibExt.AlgebraicTopology.SimplicialSpace.Presentable
import MathlibExt.CategoryTheory.NatTrans.Cardinality
import MathlibExt.CategoryTheory.SmallObject.EndpointProfile
import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# A stable cardinal envelope for the canonical local replacement

For one eligible regular cardinal `κ`, this file packages one regular endpoint
presentability cardinal `μ` and one infinite fixed-profile bound `ξ`. The
actual size bound is definitionally `γ = 2 ^ ξ`. Every derived theorem uses the
same literal auxiliary family and the same canonical
`SmallObject.terminalIteration LocalGenerators.J κ`.

The record stores chosen data only. Arithmetic, Hom, whole-label, cylinder,
accessibility, and replacement-output bounds are derived in its namespace.
-/

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace SimplicialSpace

/-- The fixed site, operator, and scalar-point profile retained by the Rezk
local-replacement cardinal envelope. -/
abbrev LocalReplacementFixedProfile : Type u :=
  ULift.{u} ((SimplexCategory × SimplexCategory)ᵒᵖ) ⊕
    (ULift.{u}
        (Σ x y : (SimplexCategory × SimplexCategory)ᵒᵖ, x ⟶ y) ⊕
      ((SSet.stdSimplex.{u}.obj ⦋0⦌).Elements ⊕
        (SSet.stdSimplex.{u}.obj ⦋1⦌).Elements))

/-- One coherent set of cardinal witnesses for the same canonical replacement
at `κ`. This is explicit data, not a typeclass. -/
structure LocalReplacementCardinalEnvelope
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ] where
  /-- The endpoint-presentability and accessibility cardinal. -/
  μ : Cardinal.{u}
  /-- Regularity of the chosen accessibility cardinal. -/
  regular_μ : Fact μ.IsRegular
  /-- The infinite fixed-profile bound. -/
  ξ : Cardinal.{u}
  /-- The accessibility cardinal is uncountable. -/
  aleph0_lt_μ : ℵ₀ < μ
  /-- The fixed-profile bound is infinite. -/
  aleph0_le_ξ : ℵ₀ ≤ ξ
  /-- The native iteration length is bounded by the fixed profile. -/
  κ_le_ξ : κ ≤ ξ
  /-- The accessibility cardinal is bounded by the fixed profile. -/
  μ_le_ξ : μ ≤ ξ
  /-- The literal site/operator/scalar profile is strictly μ-small. -/
  fixed_lt_μ : HasCardinalLT LocalReplacementFixedProfile.{u} μ
  /-- The same literal fixed profile has cardinal at most ξ. -/
  fixed_le_ξ : Cardinal.mk LocalReplacementFixedProfile.{u} ≤ ξ
  /-- The literal full auxiliary-family index is bounded by ξ. -/
  family_le_ξ :
    letI : MorphismProperty.IsSmall.{u} LocalGenerators.J.{u} :=
      SmallObject.isSmall LocalGenerators.J.{u} κ
    Cardinal.mk (Shrink.{u} LocalGenerators.J.{u}.toSet) ≤ ξ
  /-- Both endpoints of every literal auxiliary generator are μ-presentable. -/
  endpoints_presentable :
    letI : Fact μ.IsRegular := regular_μ
    ∀ i : LocalGenerators.J.{u}.toSet,
      IsCardinalPresentable.{u} i.1.left μ ∧
        IsCardinalPresentable.{u} i.1.right μ
  /-- Every original generator source has at most ξ total points. -/
  source_points_le_ξ : ∀ i : LocalGenerators.J.{u}.toSet,
    Cardinal.mk (Functor.uncurry.obj i.1.left.diagram).Elements ≤ ξ
  /-- Every original generator target has at most ξ total points. -/
  target_points_le_ξ : ∀ i : LocalGenerators.J.{u}.toSet,
    Cardinal.mk (Functor.uncurry.obj i.1.right.diagram).Elements ≤ ξ

namespace LocalReplacementCardinalEnvelope

variable {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]

/-- The stable working bound determined by the fixed-profile cardinal. -/
abbrev γ (e : LocalReplacementCardinalEnvelope κ) : Cardinal.{u} := 2 ^ e.ξ

/-- The chosen exponential bound absorbs ξ-indexed powers. -/
theorem power_eq (e : LocalReplacementCardinalEnvelope κ) :
    e.γ ^ e.ξ = e.γ := by
  dsimp [γ]
  rw [← Cardinal.power_mul, Cardinal.mul_eq_self e.aleph0_le_ξ]

/-- Cantor's theorem for the chosen fixed-profile cardinal. -/
theorem ξ_lt_γ (e : LocalReplacementCardinalEnvelope κ) : e.ξ < e.γ :=
  Cardinal.cantor e.ξ

theorem ξ_le_γ (e : LocalReplacementCardinalEnvelope κ) : e.ξ ≤ e.γ :=
  e.ξ_lt_γ.le

theorem aleph0_le_γ (e : LocalReplacementCardinalEnvelope κ) : ℵ₀ ≤ e.γ :=
  e.aleph0_le_ξ.trans e.ξ_le_γ

theorem μ_le_γ (e : LocalReplacementCardinalEnvelope κ) : e.μ ≤ e.γ :=
  e.μ_le_ξ.trans e.ξ_le_γ

/-- The actual κ-ordinal iteration length is bounded by ξ. -/
theorem κ_ord_le_ξ (e : LocalReplacementCardinalEnvelope κ) :
    Cardinal.mk κ.ord.ToType ≤ e.ξ := by
  simpa only [Cardinal.mk_ord_toType] using e.κ_le_ξ

/-- The actual μ-ordinal enlargement length is bounded by ξ. -/
theorem μ_ord_le_ξ (e : LocalReplacementCardinalEnvelope κ) :
    Cardinal.mk e.μ.ord.ToType ≤ e.ξ := by
  simpa only [Cardinal.mk_ord_toType] using e.μ_le_ξ

/-- The actual μ-ordinal enlargement length is bounded by γ. -/
theorem μ_ord_le_γ (e : LocalReplacementCardinalEnvelope κ) :
    Cardinal.mk e.μ.ord.ToType ≤ e.γ :=
  e.μ_ord_le_ξ.trans e.ξ_le_γ

/-- All operators of the actual opposite product site are strictly μ-small. -/
theorem presheafSiteOperators_lt_μ (e : LocalReplacementCardinalEnvelope κ) :
    Cardinal.mk (ULift.{u}
      (Σ x y : (SimplexCategory × SimplexCategory)ᵒᵖ, x ⟶ y)) < e.μ := by
  have h := e.fixed_lt_μ.of_injective
    (fun z : ULift.{u}
        (Σ x y : (SimplexCategory × SimplexCategory)ᵒᵖ, x ⟶ y) =>
      (Sum.inr (Sum.inl z) : LocalReplacementFixedProfile.{u}))
    (Sum.inr_injective.comp Sum.inl_injective)
  simpa only [hasCardinalLT_iff_cardinal_mk_lt] using h

/-- The same canonical replacement is accessible at the envelope's μ. -/
theorem q_isCardinalAccessible (e : LocalReplacementCardinalEnvelope κ) :
    letI : Fact e.μ.IsRegular := e.regular_μ
    (SmallObject.terminalIteration LocalGenerators.J.{u} κ).IsCardinalAccessible e.μ := by
  let _ : Fact e.μ.IsRegular := e.regular_μ
  let _ : ∀ i : LocalGenerators.J.{u}.toSet,
      IsCardinalPresentable.{u} i.1.left e.μ := fun i =>
    (e.endpoints_presentable i).1
  let _ : ∀ i : LocalGenerators.J.{u}.toSet,
      IsCardinalPresentable.{u} i.1.right e.μ := fun i =>
    (e.endpoints_presentable i).2
  exact canonical_localReplacement_isCardinalAccessible κ e.μ

/-- Every original generator-domain Hom set into a γ-small object is γ-small. -/
theorem domainHom_le (e : LocalReplacementCardinalEnvelope κ)
    (i : LocalGenerators.J.{u}.toSet) (X : SimplicialSpace.{u})
    (hX : Cardinal.mk (Functor.uncurry.obj X.diagram).Elements ≤ e.γ) :
    Cardinal.mk (i.1.left ⟶ X) ≤ e.γ := by
  let F := SimplicialSpace.toPresheaf.{u}
  have hmap : Function.Injective (fun f : i.1.left ⟶ X => F.map f) :=
    fun _ _ h => F.map_injective h
  have hX' : Cardinal.mk (F.obj X).Elements ≤ e.γ := by
    rw [← mk_totalPoints_toPresheaf X]
    exact hX
  have hA : Cardinal.mk (F.obj i.1.left).Elements ≤ e.ξ := by
    rw [← mk_totalPoints_toPresheaf i.1.left]
    exact e.source_points_le_ξ i
  have hγ0 : e.γ ≠ 0 :=
    ne_of_gt ((show 0 ≤ e.ξ from zero_le).trans_lt e.ξ_lt_γ)
  calc
    _ ≤ Cardinal.mk (F.obj i.1.left ⟶ F.obj X) :=
      Cardinal.mk_le_of_injective hmap
    _ ≤ Cardinal.mk (F.obj X).Elements ^
        Cardinal.mk (F.obj i.1.left).Elements :=
      CategoryTheory.mk_hom_le_elements_power (F.obj i.1.left) (F.obj X)
    _ ≤ e.γ ^ Cardinal.mk (F.obj i.1.left).Elements :=
      Cardinal.power_le_power_right hX'
    _ ≤ e.γ ^ e.ξ := Cardinal.power_le_power_left hγ0 hA
    _ = e.γ := e.power_eq

/-- Every literal whole label over an arrow with terminal target is γ-small.
The bottom map is determined by terminal uniqueness, while the full square
witness is retained and recovered by proof irrelevance. -/
theorem wholeLabels_le (e : LocalReplacementCardinalEnvelope κ)
    {X T : SimplicialSpace.{u}} (p : X ⟶ T) (hT : IsTerminal T)
    (hX : Cardinal.mk (Functor.uncurry.obj X.diagram).Elements ≤ e.γ) :
    Cardinal.mk (SmallObject.FunctorObjIndex
      LocalGenerators.J.{u}.homFamily p) ≤ Cardinal.lift.{u + 1} e.γ := by
  classical
  let _ : MorphismProperty.IsSmall.{u} LocalGenerators.J.{u} :=
    SmallObject.isSmall LocalGenerators.J.{u} κ
  let s : LocalGenerators.J.{u}.toSet ≃
      Shrink.{u} LocalGenerators.J.{u}.toSet :=
    equivShrink.{u} LocalGenerators.J.{u}.toSet
  let LabelCode : Type u :=
    Σ k : Shrink.{u} LocalGenerators.J.{u}.toSet,
      ((s.symm k).1.left ⟶ X)
  let encode :
      SmallObject.FunctorObjIndex LocalGenerators.J.{u}.homFamily p → LabelCode :=
    fun q =>
      ⟨s q.i,
        eqToHom (congrArg
          (fun i : LocalGenerators.J.{u}.toSet => i.1.left)
          (s.symm_apply_apply q.i)) ≫ q.t⟩
  have hencode : Function.Injective encode := by
    rintro ⟨i, top, bottom, square⟩ ⟨i', top', bottom', square'⟩ h
    have hi : i = i' := s.injective (congrArg Sigma.fst h)
    cases hi
    dsimp only [encode, LabelCode] at h
    have htMap :
        eqToHom (congrArg
          (fun i : LocalGenerators.J.{u}.toSet => i.1.left)
          (s.symm_apply_apply i)) ≫ top =
        eqToHom (congrArg
          (fun i : LocalGenerators.J.{u}.toSet => i.1.left)
          (s.symm_apply_apply i)) ≫ top' :=
      eq_of_heq (Sigma.mk.inj h).2
    have ht : top = top' :=
      (cancel_epi (eqToHom (congrArg
        (fun i : LocalGenerators.J.{u}.toSet => i.1.left)
        (s.symm_apply_apply i)))).1 htMap
    cases ht
    have hb : bottom = bottom' := hT.hom_ext _ _
    cases hb
    rfl
  have hcode (k : Shrink.{u} LocalGenerators.J.{u}.toSet) :
      Cardinal.mk ((s.symm k).1.left ⟶ X) ≤ e.γ :=
    e.domainHom_le (s.symm k) X hX
  have hLabelCode : Cardinal.mk LabelCode ≤ e.γ := by
    dsimp [LabelCode]
    rw [Cardinal.mk_sigma]
    calc
      _ ≤ Cardinal.sum (fun _ : Shrink.{u} LocalGenerators.J.{u}.toSet => e.γ) :=
        Cardinal.sum_le_sum _ _ hcode
      _ = Cardinal.mk (Shrink.{u} LocalGenerators.J.{u}.toSet) * e.γ :=
        Cardinal.sum_const' _ _
      _ ≤ e.γ :=
        Cardinal.mul_le_of_le e.aleph0_le_γ
          (e.family_le_ξ.trans e.ξ_le_γ) le_rfl
  let encodeLarge :
      SmallObject.FunctorObjIndex LocalGenerators.J.{u}.homFamily p →
        ULift.{u + 1} LabelCode :=
    fun q => ULift.up (encode q)
  have hencodeLarge : Function.Injective encodeLarge :=
    ULift.up_injective.comp hencode
  calc
    _ ≤ Cardinal.mk (ULift.{u + 1} LabelCode) :=
      Cardinal.mk_le_of_injective hencodeLarge
    _ = Cardinal.lift.{u + 1} (Cardinal.mk LabelCode) :=
      Cardinal.mk_uLift LabelCode
    _ ≤ Cardinal.lift.{u + 1} e.γ := Cardinal.lift_le.2 hLabelCode

/-- Literal labels on the chosen terminal arrow are γ-small. -/
theorem terminalLabels_le (e : LocalReplacementCardinalEnvelope κ)
    (X : SimplicialSpace.{u})
    (hX : Cardinal.mk (Functor.uncurry.obj X.diagram).Elements ≤ e.γ) :
    Cardinal.mk (SmallObject.FunctorObjIndex
      LocalGenerators.J.{u}.homFamily (terminal.from X)) ≤
        Cardinal.lift.{u + 1} e.γ :=
  e.wholeLabels_le (terminal.from X) terminalIsTerminal hX

/-- The actual inner Δ[1]-cylinder of a γ-small object is γ-small. -/
theorem innerCylinder_le (e : LocalReplacementCardinalEnvelope κ)
    (X : SimplicialSpace.{u})
    (hX : Cardinal.mk (Functor.uncurry.obj X.diagram).Elements ≤ e.γ) :
    Cardinal.mk (Functor.uncurry.obj
      ((innerTensor (SSet.stdSimplex.{u}.obj ⦋1⦌)).obj X).diagram).Elements ≤
        e.γ :=
  actual_oneSimplex_cylinder_bound X e.γ e.aleph0_le_γ hX

/-- The same canonical replacement sends every γ-small object to a γ-small
object. -/
theorem replacementPoints_le (e : LocalReplacementCardinalEnvelope κ)
    (X : SimplicialSpace.{u})
    (hX : Cardinal.mk (Functor.uncurry.obj X.diagram).Elements ≤ e.γ) :
    Cardinal.mk (Functor.uncurry.obj
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj X).diagram).Elements ≤
        e.γ := by
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  have hEq : r.Z =
      SmallObject.terminalIteration LocalGenerators.J.{u} κ :=
    SmallObject.canonical_terminal_middle_eq_terminalIteration
      LocalGenerators.J.{u} κ
  rw [← hEq]
  exact canonical_localReplacement_mk_elements_le κ e.ξ e.aleph0_le_ξ
    e.κ_le_ξ e.family_le_ξ e.source_points_le_ξ e.target_points_le_ξ X hX

end LocalReplacementCardinalEnvelope

/-- The full literal auxiliary family admits one stable cardinal envelope at
the same eligible κ. -/
theorem exists_localReplacementCardinalEnvelope
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ] :
    Nonempty (LocalReplacementCardinalEnvelope κ) := by
  let _ : IsLocallyPresentable.{u} SimplicialSpace.{u} :=
    SimplicialSpace.isLocallyPresentable
  let fixed : Type u := LocalReplacementFixedProfile.{u}
  obtain ⟨μ, hμ, hωμ, hfixedμ, hends⟩ :=
    SmallObject.original_endpoints_have_common_presentability_cardinal
      LocalGenerators.J.{u} κ fixed
  let _ : Fact μ.IsRegular := hμ
  obtain ⟨ξ, hωξ, hκξ, hμξ, hfamily, hsource, htarget, hfixedξ,
      _hpower, _hcantor⟩ :=
    SmallObject.exists_original_fixed_total_point_profile
      LocalGenerators.J.{u} κ SimplicialSpace.toPresheaf.{u} μ fixed
  refine ⟨{
    μ := μ
    regular_μ := hμ
    ξ := ξ
    aleph0_lt_μ := hωμ
    aleph0_le_ξ := hωξ
    κ_le_ξ := hκξ
    μ_le_ξ := hμξ
    fixed_lt_μ := hfixedμ
    fixed_le_ξ := hfixedξ
    family_le_ξ := hfamily
    endpoints_presentable := hends
    source_points_le_ξ := fun i => by
      rw [mk_totalPoints_toPresheaf i.1.left]
      exact hsource i
    target_points_le_ξ := fun i => by
      rw [mk_totalPoints_toPresheaf i.1.right]
      exact htarget i
  }⟩

end SimplicialSpace
