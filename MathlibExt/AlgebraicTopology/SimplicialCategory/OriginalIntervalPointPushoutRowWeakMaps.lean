/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalIntervalPointPushoutRows
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedObjectCofibrantReplacement
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalInjectiveLabelPushforwardWeakMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidClonePointPushoutMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardQuillen
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModelLeftProper
import MathlibExt.AlgebraicTopology.ModelCategory.ProperSpanGluing

/-!
# Genuine weak comparisons of the SAME original interval pushout rows

The two actual fixed-left-proper comparisons use genuine cofibrancy
only on the designated attaching leg. The actual unit-groupoid row
comparison uses the SAME whole original clone map and genuine global
point pushouts. A native original boundary-cell replacement and the
literal row square give the interval-to-unit comparison for every
original source, without assuming that the unit target is cofibrant.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.IntervalPointPushoutRows
open FixedObjects IntervalPointPushoutFrame
attribute [local instance] FixedObjectModel.modelCategory

variable {O : Type u} (x : O) {C D : FixedObjects O}
  {H K : FixedObjects OriginalTwoLabelUnitGroupoid.labels.{u}}

/-- Source-row gluing preserves the SAME original weak map when the actual interval is cofibrant. -/
theorem sourceMap_weak [IsCofibrant H] (F : C ⟶ D)
    (hF : FixedObjectModel.weakEquivalences O F) :
    FixedObjectModel.weakEquivalences (FreeObjectPointPushout.labels (O := O)) (sourceMap x (H := H) F) := by
  let _ : IsCofibrant (interval x H) := LabelPushforward.object_isCofibrant (FreeObjectPointPushout.labelMap x) H
  let _ : WeakEquivalence (LabelPushforward.map (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) F) :=
    (weakEquivalence_iff _).mpr (LabelPushforward.map_weak_of_injective
      (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) Sum.inl_injective F hF)
  have hw : WeakEquivalence (sourceMap x (H := H) F) :=
    IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
      (a := 𝟙 (⊥_ (FixedObjects (FreeObjectPointPushout.labels (O := O)))))
      (b := 𝟙 (interval x H))
      (c := LabelPushforward.map (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) F)
      (d := sourceMap x (H := H) F)
      (IsPushout.of_hasPushout (initial.to (interval x H)) (initial.to (base C)))
      (IsPushout.of_hasPushout (initial.to (interval x H)) (initial.to (base D)))
      (by simp only [Category.comp_id, Category.id_comp]) (initialIsInitial.hom_ext _ _)
      ((sourceMap_left x (H := H) F).trans (Category.id_comp _).symm) (sourceMap_right x (H := H) F)
  exact (weakEquivalence_iff _).mp hw

/-- Interval-row gluing preserves the SAME original weak map when the actual old source is cofibrant. -/
theorem intervalMap_weak [IsCofibrant C] (G : H ⟶ K)
    (hG : FixedObjectModel.weakEquivalences OriginalTwoLabelUnitGroupoid.labels.{u} G) :
    FixedObjectModel.weakEquivalences (FreeObjectPointPushout.labels (O := O)) (intervalMap x (C := C) G) := by
  let _ : IsCofibrant (base C) := LabelPushforward.object_isCofibrant
    (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) C
  let _ : WeakEquivalence (LabelPushforward.map (FreeObjectPointPushout.labelMap x) G) :=
    (weakEquivalence_iff _).mpr (LabelPushforward.map_weak_of_injective
      (FreeObjectPointPushout.labelMap x) (FreeObjectPointPushout.labelMap_injective x) G hG)
  have hw : WeakEquivalence (intervalMap x (C := C) G) :=
    IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd
      (a := 𝟙 (⊥_ (FixedObjects (FreeObjectPointPushout.labels (O := O)))))
      (b := LabelPushforward.map (FreeObjectPointPushout.labelMap x) G)
      (c := 𝟙 (base C)) (d := intervalMap x (C := C) G)
      (IsPushout.of_hasPushout (initial.to (interval x H)) (initial.to (base C)))
      (IsPushout.of_hasPushout (initial.to (interval x K)) (initial.to (base C)))
      (initialIsInitial.hom_ext _ _) (by simp only [Category.comp_id, Category.id_comp])
      (intervalMap_left x (C := C) G) ((intervalMap_right x (C := C) G).trans (Category.id_comp _).symm)
  exact (weakEquivalence_iff _).mp hw

/-- The SAME full original two-label unit interval. -/
abbrev unitInterval : FixedObjects OriginalTwoLabelUnitGroupoid.labels.{u} :=
  CodiscreteTerminal.object OriginalTwoLabelUnitGroupoid.labels.{u}

/-- The actual original unit-row source comparison is weak without a cofibrancy premise on its unit interval. -/
theorem unit_sourceMap_weak (F : C ⟶ D) (hF : FixedObjectModel.weakEquivalences O F) :
    FixedObjectModel.weakEquivalences (FreeObjectPointPushout.labels (O := O))
      (sourceMap x (H := unitInterval.{u}) F) := by
  have hs : IsPushout UnitGroupoidClone.unitPoint.{u}
      (BergnerObjects.select (C := C.val) (vertex C x))
        (intervalLeg x C unitInterval.{u}) (sourceLeg x C unitInterval.{u}) := pointSquare x C unitInterval.{u}
  have hs' : IsPushout UnitGroupoidClone.unitPoint.{u}
      (BergnerObjects.select (C := D.val) (F.val.obj (vertex C x)))
        (intervalLeg x D unitInterval.{u}) (sourceLeg x D unitInterval.{u}) :=
    (map_vertex F x).symm ▸ pointSquare x D unitInterval.{u}
  have hw := UnitGroupoidClone.unit_pushout_map_weak F.val (vertex C x) hs hs'
    (sourceMap x (H := unitInterval.{u}) F).val
      (intervalLeg_sourceMap x (H := unitInterval.{u}) F) (sourceLeg_sourceMap x (H := unitInterval.{u}) F)
        ((EnrichedDwyerKan.fixedWeak_iff F).mpr hF)
  exact (EnrichedDwyerKan.fixedWeak_iff (sourceMap x (H := unitInterval.{u}) F)).mp hw

/-- The SAME original interval-to-unit row comparison is weak for every source and genuine cofibrant weak interval. -/
theorem terminalComparison_weak [IsCofibrant H]
    (hH : FixedObjectModel.weakEquivalences OriginalTwoLabelUnitGroupoid.labels.{u} (CodiscreteTerminal.toTerminal H)) :
    FixedObjectModel.weakEquivalences (FreeObjectPointPushout.labels (O := O))
      (intervalMap x (C := C) (CodiscreteTerminal.toTerminal H)) := by
  let Q := NativeCofibrantReplacement.object C
  let _ : IsCofibrant Q := NativeCofibrantReplacement.isCofibrant C
  have hq := NativeCofibrantReplacement.q_weak C
  have ha := intervalMap_weak x (C := Q) (CodiscreteTerminal.toTerminal H) hH
  have hb := unit_sourceMap_weak x (NativeCofibrantReplacement.q C) hq
  have hc := sourceMap_weak x (H := H) (NativeCofibrantReplacement.q C) hq
  have hcomp : FixedObjectModel.weakEquivalences (FreeObjectPointPushout.labels (O := O))
      (sourceMap x (H := H) (NativeCofibrantReplacement.q C) ≫
        intervalMap x (C := C) (CodiscreteTerminal.toTerminal H)) :=
    (congrArg (fun f : object x Q H ⟶ object x C unitInterval.{u} =>
      FixedObjectModel.weakEquivalences (FreeObjectPointPushout.labels (O := O)) f)
        (comparison_square x (NativeCofibrantReplacement.q C) (CodiscreteTerminal.toTerminal H))).mp
          ((FixedObjectModel.weakEquivalences _).comp_mem _ _ ha hb)
  exact (FixedObjectModel.weakEquivalences _).of_precomp _ _ hc hcomp

/-- The SAME full original source map into the actual cofibrant weak-interval point pushout is DK weak. -/
theorem sourceLeg_weak [IsCofibrant H]
    (hH : FixedObjectModel.weakEquivalences OriginalTwoLabelUnitGroupoid.labels.{u} (CodiscreteTerminal.toTerminal H)) :
    EnrichedDwyerKan.weakEquivalences (sourceLeg x C H) := by
  have ht : EnrichedDwyerKan.weakEquivalences (sourceLeg x C unitInterval.{u}) :=
    UnitGroupoidClone.unit_pushout_weak C.val (vertex C x)
      (intervalLeg x C unitInterval.{u}) (sourceLeg x C unitInterval.{u}) (pointSquare x C unitInterval.{u})
  have hm := (EnrichedDwyerKan.fixedWeak_iff (intervalMap x (C := C) (CodiscreteTerminal.toTerminal H))).mpr
    (terminalComparison_weak x (C := C) hH)
  have hp : EnrichedDwyerKan.weakEquivalences
      (sourceLeg x C H ≫ (intervalMap x (C := C) (CodiscreteTerminal.toTerminal H)).val) :=
    (congrArg (fun f : C.val ⟶ (object x C unitInterval.{u}).val => EnrichedDwyerKan.weakEquivalences f)
      (sourceLeg_intervalMap x (C := C) (CodiscreteTerminal.toTerminal H))).mpr ht
  exact EnrichedDwyerKan.weakEquivalences.of_postcomp _ _ hm hp

end CategoryTheory.SimplicialEnrichment.IntervalPointPushoutRows
