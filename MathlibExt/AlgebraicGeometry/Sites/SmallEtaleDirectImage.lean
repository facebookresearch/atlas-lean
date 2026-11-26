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

/-!
# Direct image of abelian sheaves on small étale sites

For a scheme morphism `f : X → Y`, base change sends an étale object `U → Y` to `U ×_Y X → X`.
Precomposition defines direct image of abelian sheaves, with `(f_*F)(U) = F(U ×_Y X)`.

Restrictions and sheaf-map components are evaluated on the same base-changed objects and
arrows. This functor is additive and preserves finite limits. The scheme universe `u` and
coefficient universe `w` are independent.

See Milne, Lectures on Étale Cohomology, §8, p. 58, Lemma 8.1.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Direct image along a scheme morphism.

Precompose an abelian sheaf on `X` with the small étale base-change functor of `f : X → Y` to
obtain a sheaf on `Y`, with the same coefficient universe. -/
def smallEtaleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{w} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{w} := by
  let := smallEtaleBaseChange_isContinuous f
  exact (smallEtaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{w}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- Direct image sections are sections on the base change.

For an étale object `U → Y`, the direct-image value is `F(U ×_Y X)`, represented by the
pullback projection to `X`. -/
theorem smallEtaleDirectImage_obj_obj
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (U : Y.Etale) :
    ((smallEtaleDirectImage f).obj F).obj.obj (op U) =
      F.obj.obj (op (Scheme.Etale.mk (pullback.snd U.hom f))) := by
  rfl

/-- Direct image restrictions use the base changed arrow.

The restriction along an étale arrow `g` is the restriction of `F` along `smallEtaleBaseChange
f` applied to `g`. -/
theorem smallEtaleDirectImage_obj_map
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    {U V : Y.Etale} (g : U ⟶ V) :
    ((smallEtaleDirectImage f).obj F).obj.map g.op =
      F.obj.map ((smallEtaleBaseChange f).map g).op := by
  rfl

/-- Direct image sheaf maps evaluate on the base changed object.

The component of the direct image of a sheaf map `τ` at `U` is its component at `U ×_Y X`. -/
theorem smallEtaleDirectImage_map_app
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}
    (τ : F ⟶ G) (U : Y.Etale) :
    ((smallEtaleDirectImage f).map τ).hom.app (op U) =
      τ.hom.app (op ((smallEtaleBaseChange f).obj U)) := by
  rfl

/-- Direct image preserves identity sheaf maps.

Applying direct image to an identity morphism gives the identity of the direct-image sheaf. -/
theorem smallEtaleDirectImage_map_id
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :
    (smallEtaleDirectImage f).map (𝟙 F) = 𝟙 ((smallEtaleDirectImage f).obj F) := by
  exact (smallEtaleDirectImage f).map_id F

/-- Direct image preserves composition of sheaf maps.

Direct image of a composite sheaf morphism equals the composite of the two direct-image
morphisms. -/
theorem smallEtaleDirectImage_map_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}
    (τ : F ⟶ G) (σ : G ⟶ H) :
    (smallEtaleDirectImage f).map (τ ≫ σ) =
      (smallEtaleDirectImage f).map τ ≫ (smallEtaleDirectImage f).map σ := by
  exact (smallEtaleDirectImage f).map_comp τ σ

/-- Small étale direct image is additive.

Direct image preserves sums of abelian-sheaf morphisms. -/
theorem smallEtaleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleDirectImage.{u, w} f).Additive := by
  dsimp only [smallEtaleDirectImage, Functor.sheafPushforwardContinuous]
  infer_instance

/-- Small étale direct image is left exact.

Direct image of abelian sheaves preserves finite limits, including kernels and finite
products. -/
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

/-- Direct image formulas and functor laws.

For any scheme morphism, direct image is additive and left exact, has the base-change formulas
for sections, restrictions, and sheaf-map components, and preserves identity maps and
composition. -/
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
