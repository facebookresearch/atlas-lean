/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeRotation

/-!
# Public clients of actual Puppe rotation

These clients transport the next boundary through the weak comparison,
retain suspension reversal, act on complete Hom classes, and compose the
original source Arrow and target maps. The category-object and Hom
universes remain independent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OrdinaryHoChosenPuppe OrdinaryHoChosenPuppeRotation

namespace HomotopicalAlgebra.OrdinaryHoChosenPuppeRotationPublicClients

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (Z : C) (hZ : IsZero Z) (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone ((ι).app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

local notation "Q" => (MorphismProperty.Q (weakEquivalences C))

example (F : Arrow C) [IsCofibrant F.right]
    [Cofibration ((ι).app F.left)] [Cofibration ((ι).app F.right)]
    (hCone : weakEquivalences C (toZero Z hZ ((cone).obj F.right))) :
    letI := Localization.inverts Q (weakEquivalences C)
      (rotationComparison cone ι c hc Z hZ F)
      (rotationComparison_weak cone ι c hc Z hZ F hCone)
    inv ((Q).map (rotationComparison cone ι c hc Z hZ F)) ≫
        (Q).map (boundary cone ι c hc Z hZ (targetArrow cone ι c F)) =
      (Q).map (suspensionMap cone ι c hc Z hZ F.hom) ≫
        (suspensionReversal cone ι c hc Z hZ F.right hCone).hom := by
  let := Localization.inverts Q (weakEquivalences C)
    (rotationComparison cone ι c hc Z hZ F)
    (rotationComparison_weak cone ι c hc Z hZ F hCone)
  rw [← rotationComparison_boundary cone ι c hc Z hZ F hCone,
    ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

example (X E : C) [IsCofibrant X] [Cofibration ((ι).app X)]
    (hCone : weakEquivalences C (toZero Z hZ ((cone).obj X)))
    (g : (Q).obj (suspensionCone cone ι c Z hZ X).pt ⟶ (Q).obj E) :
    (suspensionReversal cone ι c hc Z hZ X hCone).hom ≫
        ((suspensionReversal cone ι c hc Z hZ X hCone).hom ≫ g) = g := by
  rw [← Category.assoc, suspensionReversal_involutive, Category.id_comp]

example {F G : Arrow C} (q : F ⟶ G) {E E' : C} (p : E ⟶ E')
    (g : (Q).obj (suspensionCone cone ι c Z hZ G.left).pt ⟶ (Q).obj E) :
    (Q).map (rotationComparison cone ι c hc Z hZ F) ≫
        ((Q).map (suspensionMap cone ι c hc Z hZ q.left) ≫ (g ≫ (Q).map p)) =
      (Q).map (cofiberMap cone ι c hc (targetArrowMap cone ι c hc q)) ≫
        ((Q).map (rotationComparison cone ι c hc Z hZ G) ≫ (g ≫ (Q).map p)) := by
  rw [← Category.assoc, ← Functor.map_comp, ← rotationComparison_naturality,
    Functor.map_comp, Category.assoc]

example (F : Arrow C) :
    (nextCofiberCone cone ι c F).inr ≫
        (rotationComparisonNatTrans cone ι c hc Z hZ).app F =
      boundary cone ι c hc Z hZ F :=
  rotationComparison_cofiber cone ι c hc Z hZ F

#print axioms HomotopicalAlgebra.OrdinaryHoChosenPuppeRotation.rotationComparison_weak
#print axioms HomotopicalAlgebra.OrdinaryHoChosenPuppeRotation.suspensionReversal_involutive
#print axioms HomotopicalAlgebra.OrdinaryHoChosenPuppeRotation.rotationComparison_boundary

end HomotopicalAlgebra.OrdinaryHoChosenPuppeRotationPublicClients
