/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SharpCoproductClosure
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Sharpness of products

Actual product sharpness, using the native product-pullback universal Iso.

This is for the original cell factors in Rezk6.1. Product sharpness is
derived from its actual factor; it is not a supplied attachment outcome.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkSkeletalProduct
open SharpComparisonDraft

/-- The ORIGINAL product map is the basechange of p, through both actual native Iso legs. -/
def productArrowIso {X Y : SSet.{u}} (p : X ⟶ Y) (T : SSet.{u}) :
    Arrow.mk (prod.map p (𝟙 T)) ≅
      Arrow.mk (pullback.snd p (prod.fst : Y ⨯ T ⟶ Y)) :=
  Arrow.isoMk (pullbackProdFstIsoProd p T).symm (Iso.refl _) (by
    apply prod.hom_ext
    · simp [Category.assoc]
    · simp [Category.assoc])

/-- Product with an arbitrary original cell factor preserves the actual Sharp predicate. -/
theorem product_map_sharp {X Y : SSet.{u}} (p : X ⟶ Y) (T : SSet.{u}) (hp : Sharp p) :
    Sharp (prod.map p (𝟙 T)) :=
  (SharpCoproductClosure.sharp_arrowIso_iff (productArrowIso p T)).mpr
    (SharpPullbackClosure.sharp_pullback_snd p prod.fst hp)

/-- Both forward/inverse product-pullback legs are literal native universal maps. -/
theorem productArrowIso_fourLegs {X Y : SSet.{u}} (p : X ⟶ Y) (T : SSet.{u}) :
    (productArrowIso p T).hom.left = (pullbackProdFstIsoProd p T).inv ∧
      (productArrowIso p T).hom.right = 𝟙 (Y ⨯ T) ∧
      (productArrowIso p T).inv.left = (pullbackProdFstIsoProd p T).hom ∧
      (productArrowIso p T).inv.right = 𝟙 (Y ⨯ T) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end SSet.RezkSkeletalProduct
