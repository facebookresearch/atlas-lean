/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalIntervalPointPushoutRowWeakMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalLabelEquivalencePushforward
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedLabelWeakUnitRestriction

/-!
# Genuine cobase weakness of the SAME original cofibrant weak interval at either label

The actual source-label row proves the SAME full original source map
weak. A genuine original label-equivalence transports the other selected
label with both full inverse enriched maps and actual cofibrancy/weak
unit proofs. Every supplied original pushout and its original source
arrow are retained. No Kan or global model outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.OriginalIntervalCobaseWeak
open FixedObjects
attribute [local instance] FixedObjectModel.modelCategory

variable {C D : Carrier.{u}} (H : FixedObjects OriginalTwoLabelUnitGroupoid.labels.{u}) [IsCofibrant H]

/-- Any SAME actual source-point pushout of a genuine cofibrant weak interval has its original source arrow weak. -/
theorem sourcePoint_weak (x : C) (j : H.val ⟶ D) (k : C ⟶ D)
    (sq : IsPushout (BergnerObjects.select (C := H.val) (vertex H OriginalTwoLabelUnitGroupoid.source))
      (BergnerObjects.select (C := C) x) j k)
    (hH : FixedObjectModel.weakEquivalences OriginalTwoLabelUnitGroupoid.labels.{u} (CodiscreteTerminal.toTerminal H)) :
    EnrichedDwyerKan.weakEquivalences k := by
  let S := CarrierReindexing.source C
  let e := (IntervalPointPushoutRows.pointSquare x S H).isoIsPushout _ _ sq
  have he : IntervalPointPushoutRows.sourceLeg x S H ≫ e.hom = k :=
    (IntervalPointPushoutRows.pointSquare x S H).inr_isoIsPushout_hom _ _ sq
  have hw := EnrichedDwyerKan.weakEquivalences.comp_mem _ _
    (IntervalPointPushoutRows.sourceLeg_weak x (C := S) hH)
      (EnrichedDwyerKan.weakEquivalences.of_isIso e.hom)
  exact he ▸ hw

/-- Any SAME actual point pushout at either original label has the original full source arrow genuinely DK weak. -/
theorem point_weak (s : OriginalTwoLabelUnitGroupoid.labels.{u}) (x : C) (j : H.val ⟶ D) (k : C ⟶ D)
    (sq : IsPushout (BergnerObjects.select (C := H.val) (vertex H s)) (BergnerObjects.select (C := C) x) j k)
    (hH : FixedObjectModel.weakEquivalences OriginalTwoLabelUnitGroupoid.labels.{u} (CodiscreteTerminal.toTerminal H)) :
    EnrichedDwyerKan.weakEquivalences k := by
  classical
  let e : OriginalTwoLabelUnitGroupoid.labels.{u} ≃ OriginalTwoLabelUnitGroupoid.labels.{u} :=
    Equiv.swap OriginalTwoLabelUnitGroupoid.source s
  let R := LabelRestriction.object e H
  let _ : IsCofibrant R := LabelEquivalence.restricted_isCofibrant e.symm H
  have hr := LabelRestriction.toTerminal_weak e H hH
  let p : R.val ≅ H.val := LabelEquivalence.projectionIso e.symm H
  have hsource : e OriginalTwoLabelUnitGroupoid.source = s := Equiv.swap_apply_left _ _
  have hp : BergnerObjects.select (C := R.val) (vertex R OriginalTwoLabelUnitGroupoid.source) ≫ p.hom =
      BergnerObjects.select (C := H.val) (vertex H s) :=
    (BergnerObjects.select_comp (C := R.val) (D := H.val) (vertex R OriginalTwoLabelUnitGroupoid.source) p.hom).trans
      (congrArg (BergnerObjects.select (C := H.val)) (congrArg (vertex H) hsource))
  have hs : IsPushout (BergnerObjects.select (C := R.val) (vertex R OriginalTwoLabelUnitGroupoid.source))
      (BergnerObjects.select (C := C) x) (p.hom ≫ j) k :=
    sq.of_iso (Iso.refl _) p.symm (Iso.refl _) (Iso.refl _)
      (((Iso.comp_inv_eq p).mpr hp.symm).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ j) p.inv_hom_id).trans (Category.id_comp _))).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact sourcePoint_weak R x (p.hom ≫ j) k hs hr

end CategoryTheory.SimplicialEnrichment.OriginalIntervalCobaseWeak
