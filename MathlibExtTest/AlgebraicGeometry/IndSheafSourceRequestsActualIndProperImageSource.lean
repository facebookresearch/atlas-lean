/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.IndSheafSourceRequestsActualIndProperImageSource

/-!
# Tests for the actual ind proper-image source

The proved source gives the universal property of the native ind proper-image
functor: every comparison map from the compact-generator functor factors uniquely
through it, and the factorization satisfies the left Kan extension triangle identity.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.IndSheafSourceRequestsActualIndProperImageSource

open CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
open WantedExt.AlgebraicGeometry.IndSheafSourceRequests

/-- Every comparison from the compact-generator functor factors through the
native ind proper-image functor given by the proved source. -/
example (k : Type) [Field k] {X Y : TopCat.{0}} [CompactSheafSource k X]
    [CompactSheafSource k Y] (f : X ⟶ Y) (P : CompactPushforwardSource k f)
    (G : IndSheaf k X ⥤ IndSheaf k Y)
    (β : compactPushforward k f P ⋙ Ind.yoneda ⟶ Ind.yoneda ⋙ G) :
    ∃ ψ : indProperImage k f P (actual_ind_proper_image_source k X Y f P) ⟶ G,
      compactPushforwardUnit k f P (actual_ind_proper_image_source k X Y f P) ≫
        Functor.whiskerLeft Ind.yoneda ψ = β := by
  have D := actual_ind_proper_image_source k X Y f P
  have := D.hasKan
  have hKan : (indProperImage k f P D).IsLeftKanExtension
      (compactPushforwardUnit k f P D) := by
    unfold indProperImage compactPushforwardUnit
    infer_instance
  exact ⟨Functor.descOfIsLeftKanExtension _ (compactPushforwardUnit k f P D) G β,
    Functor.descOfIsLeftKanExtension_fac _ (compactPushforwardUnit k f P D) G β⟩

/-- The factorization through the native ind proper-image functor is unique. -/
example (k : Type) [Field k] {X Y : TopCat.{0}} [CompactSheafSource k X]
    [CompactSheafSource k Y] (f : X ⟶ Y) (P : CompactPushforwardSource k f)
    (G : IndSheaf k X ⥤ IndSheaf k Y)
    (β : compactPushforward k f P ⋙ Ind.yoneda ⟶ Ind.yoneda ⋙ G)
    (ψ₁ ψ₂ : indProperImage k f P (actual_ind_proper_image_source k X Y f P) ⟶ G)
    (h₁ : compactPushforwardUnit k f P (actual_ind_proper_image_source k X Y f P) ≫
      Functor.whiskerLeft Ind.yoneda ψ₁ = β)
    (h₂ : compactPushforwardUnit k f P (actual_ind_proper_image_source k X Y f P) ≫
      Functor.whiskerLeft Ind.yoneda ψ₂ = β) : ψ₁ = ψ₂ := by
  have D := actual_ind_proper_image_source k X Y f P
  have := D.hasKan
  have hKan : (indProperImage k f P D).IsLeftKanExtension
      (compactPushforwardUnit k f P D) := by
    unfold indProperImage compactPushforwardUnit
    infer_instance
  exact Functor.hom_ext_of_isLeftKanExtension _ (compactPushforwardUnit k f P D) _ _
    (h₁.trans h₂.symm)

end MathlibExtTest.AlgebraicGeometry.IndSheafSourceRequestsActualIndProperImageSource
