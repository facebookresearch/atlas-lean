/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Subfunctor.Cardinality
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The canonical diagram of bounded subpresheaves

The literal subtype of original subfunctors is indexed by the total-point
cardinal bound. Its diagram and cocone use the original native inclusions.
These data are defined for every cardinal, without a regularity or presentation
premise. Source: the elementary fixed-site presheaf support construction used
in the Hirschhorn localization/cardinality route.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite Cardinal

namespace CategoryTheory.Subfunctor

variable {C : Type} [SmallCategory C] (F : Cᵒᵖ ⥤ Type u)

/-- The literal subtype of original subfunctors with fewer than μ total points. -/
abbrev CardinalLTIndex (μ : Cardinal.{u}) : Type u :=
  {U : Subfunctor F // Cardinal.mk U.toFunctor.Elements < μ}

/-- The original inclusion diagram, with its native subtype preorder category. -/
@[simps! obj map]
def cardinalLTDiagram (μ : Cardinal.{u}) : CardinalLTIndex F μ ⥤ Cᵒᵖ ⥤ Type u where
  obj U := U.val.toFunctor
  map h := homOfLe (leOfHom h)
  map_id U := by
    ext X x
    rfl
  map_comp f g := by
    ext X x
    rfl

/-- The actual original inclusion cocone to F. -/
@[simps! pt ι_app]
def cardinalLTCocone (μ : Cardinal.{u}) : Cocone (cardinalLTDiagram F μ) where
  pt := F
  ι :=
    { app U := U.val.ι
      naturality := by
        intro U V h
        change homOfLe (leOfHom h) ≫ V.val.ι = U.val.ι ≫ 𝟙 F
        simpa only [Category.comp_id] using homOfLe_ι (leOfHom h) }

private theorem cardinalLTIndex_filtered (μ : Cardinal.{u}) [Fact μ.IsRegular] :
    IsCardinalFiltered (CardinalLTIndex F μ) μ := by
  apply isCardinalFiltered_preorder (CardinalLTIndex F μ) μ
  intro K s hK
  let U : Subfunctor F := ⨆ k, (s k).val
  have hU : Cardinal.mk U.toFunctor.Elements < μ :=
    mk_elements_iSup_lt_of_isRegular (fun k => (s k).val) Fact.out hK
      (fun k => (s k).property)
  refine ⟨⟨U, hU⟩, ?_⟩
  intro k
  exact le_iSup (fun k => (s k).val) k

private theorem cardinalLT_orbit_bound (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) < μ)
    {X : Cᵒᵖ} (x : F.obj X) :
    Cardinal.mk (ofSection x).toFunctor.Elements < μ := by
  have hGen : (ofSection x).IsGeneratedBy (fun _ : PUnit.{u + 1} => x) := by
    simp only [IsGeneratedBy, iSup_const]
  have hOne : Cardinal.mk PUnit.{u + 1} < μ := by
    simpa only [Cardinal.mk_punit, Nat.cast_one] using
      (Cardinal.IsRegular.nat_lt Fact.out 1)
  exact hGen.mk_elements_lt (Cardinal.IsRegular.aleph0_le Fact.out) hOne hOp

/-- The same literal index is μ-filtered and its same original cocone is colimiting. -/
theorem cardinalLTIndex_presentation (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) < μ) :
    IsCardinalFiltered (CardinalLTIndex F μ) μ ∧
      Nonempty (IsColimit (cardinalLTCocone F μ)) := by
  have hJ := cardinalLTIndex_filtered F μ
  let _ : IsCardinalFiltered (CardinalLTIndex F μ) μ := hJ
  let _ : IsFiltered (CardinalLTIndex F μ) :=
    isFiltered_of_isCardinalFiltered (CardinalLTIndex F μ) μ
  refine ⟨hJ, ⟨?_⟩⟩
  apply evaluationJointlyReflectsColimits
  intro X
  apply Types.FilteredColimit.isColimitOf'
    (cardinalLTDiagram F μ ⋙ (evaluation Cᵒᵖ (Type u)).obj X)
    (((evaluation Cᵒᵖ (Type u)).obj X).mapCocone (cardinalLTCocone F μ))
  · intro x
    let U : CardinalLTIndex F μ :=
      ⟨ofSection x, cardinalLT_orbit_bound F μ hOp x⟩
    exact ⟨U, ⟨x, mem_ofSection_obj x⟩, rfl⟩
  · intro U x y h
    have hxy : x = y := by
      apply Subtype.ext
      exact h
    refine ⟨U, 𝟙 U, ?_⟩
    simpa only [Functor.map_id, types_id_apply] using hxy

end CategoryTheory.Subfunctor

namespace CategoryTheory.Functor

variable {C : Type} [SmallCategory C]

/-- One original bounded subfunctor supports every supplied target point at once. -/
theorem exists_bounded_subfunctor_support
    (T : (Cᵒᵖ ⥤ Type u) ⥤ Cᵒᵖ ⥤ Type u) (F : Cᵒᵖ ⥤ Type u)
    (μ γ : Cardinal.{u}) [Fact μ.IsRegular] [T.IsCardinalAccessible μ]
    (hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) < μ)
    (hμγ : μ ≤ γ) (S : Set (T.obj F).Elements) (hS : Cardinal.mk S ≤ γ) :
    ∃ U : Subfunctor F, Cardinal.mk U.toFunctor.Elements ≤ γ ∧
      ∃ φ : S → (T.obj U.toFunctor).Elements,
        ((T.map U.ι).mapElements).obj ∘ φ = Subtype.val := by
  obtain ⟨hJ, ⟨hc⟩⟩ := Subfunctor.cardinalLTIndex_presentation F μ hOp
  let _ : IsCardinalFiltered (Subfunctor.CardinalLTIndex F μ) μ := hJ
  let _ : PreservesColimitsOfShape (Subfunctor.CardinalLTIndex F μ) T :=
    preservesColimitsOfShape_of_isCardinalAccessible T μ
      (Subfunctor.CardinalLTIndex F μ)
  have hTc : IsColimit (T.mapCocone (Subfunctor.cardinalLTCocone F μ)) :=
    isColimitOfPreserves T hc
  have hRep (s : S) :
      ∃ U : Subfunctor.CardinalLTIndex F μ,
        ∃ x : (T.obj U.val.toFunctor).obj s.val.obj,
          (T.map U.val.ι).app s.val.obj x = s.val.val := by
    have hEval := isColimitOfPreserves
      ((evaluation Cᵒᵖ (Type u)).obj s.val.obj) hTc
    exact Types.jointly_surjective_of_isColimit hEval s.val.val
  choose V a ha using hRep
  let U : Subfunctor F := ⨆ s : S, (V s).val
  have hγ : ℵ₀ ≤ γ := (Cardinal.IsRegular.aleph0_le Fact.out).trans hμγ
  have hU : Cardinal.mk U.toFunctor.Elements ≤ γ :=
    Subfunctor.mk_elements_iSup_le_of_le (fun s : S => (V s).val) hγ hS
      (fun s => (V s).property.le.trans hμγ)
  let inclusion (s : S) : (V s).val.toFunctor ⟶ U.toFunctor :=
    Subfunctor.homOfLe (le_iSup (fun s : S => (V s).val) s)
  let φ : S → (T.obj U.toFunctor).Elements := fun s =>
    Functor.elementsMk (T.obj U.toFunctor) s.val.obj
      ((T.map (inclusion s)).app s.val.obj (a s))
  refine ⟨U, hU, φ, ?_⟩
  funext s
  apply Functor.Elements.ext
    (((T.map U.ι).mapElements).obj (φ s)) s.val rfl
  have hcomp : T.map (inclusion s) ≫ T.map U.ι = T.map (V s).val.ι := by
    rw [← T.map_comp]
    exact congrArg T.map (Subfunctor.homOfLe_ι
      (le_iSup (fun s : S => (V s).val) s))
  have hpoint := congrArg (fun q => q.app s.val.obj (a s)) hcomp
  change (T.obj F).map (𝟙 s.val.obj)
      ((T.map U.ι).app s.val.obj
        ((T.map (inclusion s)).app s.val.obj (a s))) = s.val.val
  simpa only [eqToHom_refl, Functor.map_id, types_id_apply, NatTrans.comp_app,
    types_comp_apply] using
    hpoint.trans (ha s)

end CategoryTheory.Functor
