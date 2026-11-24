/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Subfunctor.CardinalPresentation

/-! # Original inclusion and transition data

The canonical bounded-subpresheaf cocone retains original points and inclusion
maps, including the identity transition for equal same-stage images.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite Cardinal

namespace CategoryTheory.Subfunctor.CardinalPresentationTest

variable {C : Type} [SmallCategory C] (F : Cᵒᵖ ⥤ Type u)

/-- The canonical leg is exactly the original point inclusion. -/
theorem original_inclusion (μ : Cardinal.{u})
    (U : Subfunctor.CardinalLTIndex F μ) (X : Cᵒᵖ) (x : U.val.toFunctor.obj X) :
    ((Subfunctor.cardinalLTCocone F μ).ι.app U).app X x = x.val := rfl

/-- The original diagram map keeps the underlying point and original inclusion equation. -/
theorem original_transition (μ : Cardinal.{u})
    {U V : Subfunctor.CardinalLTIndex F μ} (h : U ⟶ V)
    (X : Cᵒᵖ) (x : U.val.toFunctor.obj X) :
    (((Subfunctor.cardinalLTDiagram F μ).map h).app X x).val = x.val ∧
      (Subfunctor.cardinalLTDiagram F μ).map h ≫ V.val.ι = U.val.ι :=
  ⟨rfl, Subfunctor.homOfLe_ι (leOfHom h)⟩

/-- Equal original same-stage images have the actual identity transition as witness. -/
theorem same_stage_eventual_equality (μ : Cardinal.{u})
    (U : Subfunctor.CardinalLTIndex F μ) (X : Cᵒᵖ)
    (x y : U.val.toFunctor.obj X)
    (h : ((Subfunctor.cardinalLTCocone F μ).ι.app U).app X x =
      ((Subfunctor.cardinalLTCocone F μ).ι.app U).app X y) :
    ∃ V : Subfunctor.CardinalLTIndex F μ, ∃ f : U ⟶ V,
      ((Subfunctor.cardinalLTDiagram F μ).map f).app X x =
        ((Subfunctor.cardinalLTDiagram F μ).map f).app X y := by
  have hxy : x = y := Subtype.ext h
  exact ⟨U, 𝟙 U, congrArg _ hxy⟩

/-- Every supplied small original family has an actual upper-bound index. -/
theorem original_family_upper_bound (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) < μ)
    {K : Type u} (s : K → Subfunctor.CardinalLTIndex F μ)
    (hK : Cardinal.mk K < μ) :
    ∃ U : Subfunctor.CardinalLTIndex F μ, ∀ k, s k ≤ U := by
  have hJ := (Subfunctor.cardinalLTIndex_presentation F μ hOp).1
  let _ : IsCardinalFiltered (Subfunctor.CardinalLTIndex F μ) μ := hJ
  have hCard : HasCardinalLT K μ :=
    (hasCardinalLT_iff_cardinal_mk_lt K μ).2 hK
  refine ⟨IsCardinalFiltered.max s hCard, ?_⟩
  intro k
  exact leOfHom (IsCardinalFiltered.toMax s hCard k)

/-- An original point has a same-object representative through the actual cocone. -/
theorem original_point_representative (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) < μ)
    (X : Cᵒᵖ) (x : F.obj X) :
    ∃ U : Subfunctor.CardinalLTIndex F μ,
      ∃ y : U.val.toFunctor.obj X,
        ((Subfunctor.cardinalLTCocone F μ).ι.app U).app X y = x := by
  obtain ⟨_, ⟨hc⟩⟩ := Subfunctor.cardinalLTIndex_presentation F μ hOp
  have hEval := isColimitOfPreserves ((evaluation Cᵒᵖ (Type u)).obj X) hc
  exact Types.jointly_surjective_of_isColimit hEval x

end CategoryTheory.Subfunctor.CardinalPresentationTest

namespace CategoryTheory.Subfunctor.CardinalPresentationTest

universe v
variable {C : Type} [SmallCategory C] (F : Cᵒᵖ ⥤ Type u)

/-- Empty requested support retains the same exact elements-map equation. -/
theorem empty_requested_support
    (T : (Cᵒᵖ ⥤ Type u) ⥤ Cᵒᵖ ⥤ Type u) (μ γ : Cardinal.{u})
    [Fact μ.IsRegular] [T.IsCardinalAccessible μ]
    (hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) < μ) (hμγ : μ ≤ γ) :
    ∃ U : Subfunctor F, Cardinal.mk U.toFunctor.Elements ≤ γ ∧
      ∃ φ : (∅ : Set (T.obj F).Elements) → (T.obj U.toFunctor).Elements,
        ((T.map U.ι).mapElements).obj ∘ φ = Subtype.val :=
  T.exists_bounded_subfunctor_support F μ γ hOp hμγ ∅ (by simp)

/-- Every requested point keeps its original object and uses the same simultaneous witness. -/
theorem requested_point_same_object
    (T : (Cᵒᵖ ⥤ Type u) ⥤ Cᵒᵖ ⥤ Type u) (μ γ : Cardinal.{u})
    [Fact μ.IsRegular] [T.IsCardinalAccessible μ]
    (hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) < μ) (hμγ : μ ≤ γ)
    (S : Set (T.obj F).Elements) (hS : Cardinal.mk S ≤ γ) (s : S) :
    ∃ U : Subfunctor F, Cardinal.mk U.toFunctor.Elements ≤ γ ∧
      ∃ φ : S → (T.obj U.toFunctor).Elements,
        ((T.map U.ι).mapElements).obj ∘ φ = Subtype.val ∧
        (φ s).obj = s.val.obj ∧
        ((T.map U.ι).mapElements).obj (φ s) = s.val := by
  obtain ⟨U, hU, φ, hφ⟩ := T.exists_bounded_subfunctor_support F μ γ hOp hμγ S hS
  have hs : ((T.map U.ι).mapElements).obj (φ s) = s.val := congrFun hφ s
  exact ⟨U, hU, φ, hφ, congrArg (fun e : (T.obj F).Elements => e.obj) hs, hs⟩

/-- Any originally labelled family into S factors through the same bounded support. -/
theorem original_family_factorization
    (T : (Cᵒᵖ ⥤ Type u) ⥤ Cᵒᵖ ⥤ Type u) (μ γ : Cardinal.{u})
    [Fact μ.IsRegular] [T.IsCardinalAccessible μ]
    (hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) < μ) (hμγ : μ ≤ γ)
    (S : Set (T.obj F).Elements) (hS : Cardinal.mk S ≤ γ)
    {A : Type v} (a : A → S) :
    ∃ U : Subfunctor F, Cardinal.mk U.toFunctor.Elements ≤ γ ∧
      ∃ φ : S → (T.obj U.toFunctor).Elements,
        ((T.map U.ι).mapElements).obj ∘ φ = Subtype.val ∧
        (((T.map U.ι).mapElements).obj ∘ φ) ∘ a = Subtype.val ∘ a := by
  obtain ⟨U, hU, φ, hφ⟩ := T.exists_bounded_subfunctor_support F μ γ hOp hμγ S hS
  exact ⟨U, hU, φ, hφ,
    congrArg (fun k : S → (T.obj F).Elements => k ∘ a) hφ⟩

end CategoryTheory.Subfunctor.CardinalPresentationTest
