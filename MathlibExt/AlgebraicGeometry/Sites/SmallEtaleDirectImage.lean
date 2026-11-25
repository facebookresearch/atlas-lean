/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleBaseChangeContinuity
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Limits

/-! # Direct image on the original small étale sites

Milne, *Lectures on Étale Cohomology*, §8, page 58, Lemma 8.1: base change
along a scheme morphism gives a direct-image functor on actual abelian sheaves.
Its sections, restrictions, and sheaf-morphism components are the literal
precomposition formulas, in every independent coefficient universe.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The actual direct-image functor for an arbitrary scheme morphism and
arbitrary coefficient universe, obtained from proved original-site continuity. -/
def smallEtaleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{w} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{w} := by
  let := smallEtaleBaseChange_isContinuous f
  exact (smallEtaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{w}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- Sections of the actual direct image are sections on the literal fiber
product object over the original source scheme. -/
theorem smallEtaleDirectImage_obj_obj
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (U : Y.Etale) :
    ((smallEtaleDirectImage f).obj F).obj.obj (op U) =
      F.obj.obj (op (Scheme.Etale.mk (pullback.snd U.hom f))) := by
  rfl

/-- Restriction along an actual small-site map is the original restriction
along its actual base-change map. -/
theorem smallEtaleDirectImage_obj_map
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    {U V : Y.Etale} (g : U ⟶ V) :
    ((smallEtaleDirectImage f).obj F).obj.map g.op =
      F.obj.map ((smallEtaleBaseChange f).map g).op := by
  rfl

/-- Every direct-image sheaf-morphism component is the original component
at the actual base-change object. -/
theorem smallEtaleDirectImage_map_app
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}
    (τ : F ⟶ G) (U : Y.Etale) :
    ((smallEtaleDirectImage f).map τ).hom.app (op U) =
      τ.hom.app (op ((smallEtaleBaseChange f).obj U)) := by
  rfl

/-- The stock induced sheaf functor preserves actual identity morphisms. -/
theorem smallEtaleDirectImage_map_id
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :
    (smallEtaleDirectImage f).map (𝟙 F) = 𝟙 ((smallEtaleDirectImage f).obj F) := by
  exact (smallEtaleDirectImage f).map_id F

/-- The stock induced sheaf functor preserves every actual sheaf-morphism
composition. -/
theorem smallEtaleDirectImage_map_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}
    (τ : F ⟶ G) (σ : G ⟶ H) :
    (smallEtaleDirectImage f).map (τ ≫ σ) =
      (smallEtaleDirectImage f).map τ ≫ (smallEtaleDirectImage f).map σ := by
  exact (smallEtaleDirectImage f).map_comp τ σ

/-- Additivity comes from the stock additive precomposition and full-subcategory
lift providers, in every independent coefficient universe. -/
theorem smallEtaleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleDirectImage.{u, w} f).Additive := by
  dsimp only [smallEtaleDirectImage, Functor.sheafPushforwardContinuous]
  infer_instance

/-- The actual direct image is left exact: forgetful functors create sheaf
limits and the literal presheaf precomposition preserves finite limits. -/
theorem smallEtaleDirectImage_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (smallEtaleDirectImage.{u, w} f) := by
  let V := sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{w}
  let : PreservesFiniteLimits (smallEtaleDirectImage.{u, w} f ⋙ V) := by
    change PreservesFiniteLimits
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{w} ⋙
        (Functor.whiskeringLeft Y.Etaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{w}).obj
          (smallEtaleBaseChange f).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (smallEtaleDirectImage.{u, w} f) V

/-- One actual additive, left exact direct-image functor has all the literal
section, restriction, sheaf-morphism, and functor-law formulas simultaneously. -/
theorem original_small_etale_direct_image {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let D := smallEtaleDirectImage.{u, w} f
    D.Additive ∧ PreservesFiniteLimits D ∧
      (∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (U : Y.Etale),
        (D.obj F).obj.obj (op U) =
          F.obj.obj (op (Scheme.Etale.mk (pullback.snd U.hom f)))) ∧
      (∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
          (U V : Y.Etale) (g : U ⟶ V),
        (D.obj F).obj.map g.op = F.obj.map ((smallEtaleBaseChange f).map g).op) ∧
      (∀ (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (τ : F ⟶ G) (U : Y.Etale),
        (D.map τ).hom.app (op U) = τ.hom.app (op ((smallEtaleBaseChange f).obj U))) ∧
      (∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w},
        D.map (𝟙 F) = 𝟙 (D.obj F)) ∧
      ∀ (F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
        (τ : F ⟶ G) (σ : G ⟶ H), D.map (τ ≫ σ) = D.map τ ≫ D.map σ := by
  dsimp only
  exact ⟨smallEtaleDirectImage_additive f, smallEtaleDirectImage_preservesFiniteLimits f,
    (fun F U => smallEtaleDirectImage_obj_obj f F U),
    (fun F U V g => smallEtaleDirectImage_obj_map f F g),
    (fun F G τ U => smallEtaleDirectImage_map_app f τ U),
    (fun F => smallEtaleDirectImage_map_id f F),
    (fun F G H τ σ => smallEtaleDirectImage_map_comp f τ σ)⟩

end AlgebraicGeometry.Scheme.DerivedSections
