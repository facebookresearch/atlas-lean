/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontGadgetNerveWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNativeGadgetRawHomComparison

/-!
# The SAME original fixed-front raw-Hom input augmentation is weak

Every original fixed-front input contributes its complete original raw
endpoint Hom and its literal input map. The actual full gadget index
map and its augmentation square transfer the proved original gadget
augmentation to this same original diagram at quasicategory targets.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

open OriginalPointed OriginalGadgetComparison

/-- Every full original fixed-front input retains the same entire original raw-Hom coefficient. -/
def fixedFrontRawInputDiagram (X : OriginalPointed.Category.{u}) :
    CostructuredArrow plainFixedFrontDiagram X ⥤ SSet.{u} :=
  CostructuredArrow.proj plainFixedFrontDiagram X ⋙ plainFixedFrontDiagram ⋙ homFunctor

/-- The actual complete original fixed-front input raw-Hom augmentation uses the SAME original input Hom maps. -/
def fixedFrontRawInputAugmentation (X : OriginalPointed.Category.{u}) :
    fixedFrontRawInputDiagram X ⟶
      (CategoryTheory.Functor.const (CostructuredArrow plainFixedFrontDiagram X)).obj (homObject X) where
  app s := homFunctor.map s.hom
  naturality s t f := by
    have h : homFunctor.map (plainFixedFrontDiagram.map f.left) ≫ homFunctor.map t.hom = homFunctor.map s.hom :=
      (homFunctor.map_comp _ _).symm.trans (congrArg homFunctor.map (CostructuredArrow.w f))
    exact h.trans (Category.comp_id _).symm

/-- The full original fixed-front coefficient diagram is retained literally by the same gadget input functor. -/
def fixedFrontRawInputToGadgets (X : OriginalPointed.Category.{u}) :
    fixedFrontRawInputDiagram X ⋙ SSet.uliftFunctor.{u+1,u} ⟶
      fixedFrontIntoGadgetInputs X ⋙ liftedRawHomDiagram X where
  app s := 𝟙 (SSet.uliftFunctor.{u+1,u}.obj (homObject (plainFixedFrontDiagram.obj s.left)))
  naturality s t f := by
    change SSet.uliftFunctor.map (homFunctor.map (plainFixedFrontDiagram.map f.left)) ≫ 𝟙 _ =
      𝟙 _ ≫ SSet.uliftFunctor.map (homFunctor.map (plainFixedFrontDiagram.map f.left))
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Every whole original fixed-front input retains its SAME actual raw-Hom augmentation triangle. -/
theorem fixedFrontRawInputToGadgets_augmentation (X : OriginalPointed.Category.{u})
    (s : CostructuredArrow plainFixedFrontDiagram X) :
    (fixedFrontRawInputToGadgets X).app s ≫ (liftedRawHomInputAugmentation X).app
      ((fixedFrontIntoGadgetInputs X).obj s) =
        SSet.uliftFunctor.{u+1,u}.map ((fixedFrontRawInputAugmentation X).app s) ≫ 𝟙 _ :=
  (Category.id_comp _).trans (Category.comp_id _).symm

/-- The SAME original full fixed-front raw-Hom BK index map is weak at every original quasicategory target. -/
theorem fixedFrontRawInputIndexMap_weak (X : OriginalPointed.Category.{u}) [SSet.Quasicategory X.right] :
    SSet.realizationWeakEquivalences (SSet.bkHocolimIndexMapULift.{u,u+1,0,u}
      (fixedFrontIntoGadgetInputs X) (fixedFrontRawInputToGadgets X)) :=
  SSet.bkHocolimIndexMapULift_weak_of_pointCoefficients.{u,u+1,0,u} _ _
    (fun s => (fixedFrontDegree_mappingGadget s.left).1)
    (liftedRawHomDiagram_point_weak X) (fixedFrontIntoGadgetInputs_nerve_weak X)

/-- The SAME actual original fixed-front raw-Hom input BK augmentation is weak for every original quasicategory and both
original endpoints. -/
theorem fixedFrontRawInputAugmentation_weak (K : SSet.{u}) [SSet.Quasicategory K] (x y : K _⦋0⦌) :
    SSet.realizationWeakEquivalences (SSet.bkAugmentation
      (fixedFrontRawInputAugmentation (Under.mk (SSet.boundaryOneMap x y)))) := by
  let X : OriginalPointed.Category.{u} := Under.mk (SSet.boundaryOneMap x y)
  let _ : SSet.Quasicategory X.right := ‹SSet.Quasicategory K›
  have hSquare := SSet.bkHocolimIndexMapULift_augmentationSquare.{u,u+1,0,u}
    (fixedFrontIntoGadgetInputs X) (fixedFrontRawInputToGadgets X)
    (fixedFrontRawInputAugmentation X) (liftedRawHomInputAugmentation X) (𝟙 _)
    (fixedFrontRawInputToGadgets_augmentation X)
  have hIndex := fixedFrontRawInputIndexMap_weak X
  have hG := rawHomHocolimAugmentation_weak K x y
  have hComposite := SSet.realizationWeakEquivalences.comp_mem _ _ hIndex hG
  have hLift : SSet.realizationWeakEquivalences
      (SSet.uliftFunctor.{u+1,u}.map (SSet.bkAugmentation (fixedFrontRawInputAugmentation X))) :=
    (Category.comp_id (SSet.uliftFunctor.{u+1,u}.map
      (SSet.bkAugmentation (fixedFrontRawInputAugmentation X)))) ▸ (hSquare ▸ hComposite)
  exact (SSet.realizationWeak_ulift_map_iff.{u,u+1}
    (SSet.bkAugmentation (fixedFrontRawInputAugmentation X))).mp hLift

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
