/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalReedyGadgetInputComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveULiftToTargetNaturality

/-!
# The SAME full original fixed-front gadget input nerve map is weak

The actual Reedy input map is weak, its complete original restriction
is weak, and the same generated pointed map gives their full original
input natural transformation. Its nerve homotopy proves weakness of
the SAME fixed-front input map with all original universes retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite

attribute [local instance] CategoryTheory.uliftCategory

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The same full original Reedy-to-gadget nerve map is weak with its actual original coefficient universe lift. -/
theorem reedyIntoGadgetInputs_nerve_weak (X : OriginalPointed.Category.{u}) [SSet.Quasicategory X.right] :
    SSet.realizationWeakEquivalences
      (SSet.nerveMapULiftToTarget.{u,u+1,0,u} (reedyIntoGadgetInputs X)) := by
  have hR := OriginalGadgetComparison.reedyIntoGadgetInputs_liftedNerve_weak X
  have h := SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso
      (nerveObjectHomULiftIso.{u,0,u+1,u} (CostructuredArrow plainReedyDiagram X)).hom) hR
  exact SSet.nerveMapULiftToTarget_sourceLift.{u,u+1,0,u} (reedyIntoGadgetInputs X) ▸ h

/-- The SAME original fixed-front full gadget input nerve map is weak at every original quasicategory target. -/
theorem fixedFrontIntoGadgetInputs_nerve_weak (X : OriginalPointed.Category.{u}) [SSet.Quasicategory X.right] :
    SSet.realizationWeakEquivalences
      (SSet.nerveMapULiftToTarget.{u,u+1,0,u} (fixedFrontIntoGadgetInputs X)) := by
  let L : ULift.{u+1} (ULiftHom.{u} (CostructuredArrow plainReedyDiagram X)) ⥤
      CostructuredArrow plainReedyDiagram X :=
    ULift.downFunctor.{u,u,u+1} ⋙ ULiftHom.down.{0,u,u}
  have hNat := NatTrans.nerveHomotopy (Functor.whiskerLeft L (reedyInputGadgetComparison X))
  have hR : SSet.realizationWeakEquivalences (nerveMap (L ⋙ reedyIntoGadgetInputs X)) :=
    OriginalGadgetComparison.reedyIntoGadgetInputs_liftedNerve_weak X
  have hLeft := (SSet.realizationWeakEquivalences_iff_of_homotopy hNat).mpr hR
  have hComposite := SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso
      (nerveObjectHomULiftIso.{u,0,u+1,u} (CostructuredArrow plainReedyDiagram X)).hom) hLeft
  have hComposite' : SSet.realizationWeakEquivalences (SSet.nerveMapULiftToTarget.{u,u+1,0,u}
      (reedyInputRestriction X ⋙ fixedFrontIntoGadgetInputs X)) :=
    SSet.nerveMapULiftToTarget_sourceLift.{u,u+1,0,u}
      (reedyInputRestriction X ⋙ fixedFrontIntoGadgetInputs X) ▸ hComposite
  have hRestriction := (SSet.realizationWeak_ulift_map_iff.{u,u+1}
    (nerveMap (reedyInputRestriction X))).mpr (reedyInputRestriction_nerve_weak X)
  exact SSet.realizationWeakEquivalences.of_precomp _ _ hRestriction
    ((SSet.nerveMapULiftToTarget_precomp.{u,u+1,0,u}
      (reedyInputRestriction X) (fixedFrontIntoGadgetInputs X)).symm ▸ hComposite')

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
