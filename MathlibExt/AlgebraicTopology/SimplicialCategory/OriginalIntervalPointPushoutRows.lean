/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalIntervalPointPushoutFrame
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelCarrierUnitNaturality

/-!
# The SAME whole original interval rows and their source/interval comparisons

Every row is the actual fixed-label pushout whose genuine global
point-pushout property is already proved. Both complete source and
interval maps use the original label-pushforward functors. All four
original naturality triangles and the actual row square are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.IntervalPointPushoutRows
open FixedObjects IntervalPointPushoutFrame

variable {O : Type u} (x : O) (C : FixedObjects O)
  (H : FixedObjects OriginalTwoLabelUnitGroupoid.labels.{u})

/-- The SAME genuine original fixed-label pushout row. -/
abbrev object : FixedObjects (FreeObjectPointPushout.labels (O := O)) :=
  pushout (initial.to (interval x H)) (initial.to (base C))

/-- The complete original interval map into its SAME actual row. -/
def intervalLeg : H.val ⟶ (object x C H).val :=
  LabelPushforward.carrierUnit (FreeObjectPointPushout.labelMap x) H ≫
    (pushout.inl (initial.to (interval x H)) (initial.to (base C))).val

/-- The complete original source map into its SAME actual row. -/
def sourceLeg : C.val ⟶ (object x C H).val :=
  LabelPushforward.carrierUnit (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) C ≫
    (pushout.inr (initial.to (interval x H)) (initial.to (base C))).val

/-- The SAME entire original row is genuinely the actual original point pushout. -/
theorem pointSquare : IsPushout
    (BergnerObjects.select (C := H.val) (vertex H OriginalTwoLabelUnitGroupoid.source))
    (BergnerObjects.select (C := C.val) (vertex C x)) (intervalLeg x C H) (sourceLeg x C H) :=
  IntervalPointPushoutFrame.isPushout x C H (IsPushout.of_hasPushout _ _)

variable {C H} {D : FixedObjects O}
  {K : FixedObjects OriginalTwoLabelUnitGroupoid.labels.{u}}

/-- The SAME full original source comparison between the two actual pushout rows. -/
def sourceMap (F : C ⟶ D) : object x C H ⟶ object x D H :=
  pushout.map (initial.to (interval x H)) (initial.to (base C))
    (initial.to (interval x H)) (initial.to (base D)) (𝟙 (interval x H))
    (LabelPushforward.map (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) F) (𝟙 _)
    (by simp only [Category.comp_id, Category.id_comp]) (initialIsInitial.hom_ext _ _)

/-- The SAME full original interval comparison between the two actual pushout rows. -/
def intervalMap (G : H ⟶ K) : object x C H ⟶ object x C K :=
  pushout.map (initial.to (interval x H)) (initial.to (base C))
    (initial.to (interval x K)) (initial.to (base C))
      (LabelPushforward.map (FreeObjectPointPushout.labelMap x) G) (𝟙 (base C)) (𝟙 _)
        (initialIsInitial.hom_ext _ _) (by simp only [Category.comp_id, Category.id_comp])

/-- The actual source comparison retains the entire original left pushout leg. -/
theorem sourceMap_left (F : C ⟶ D) :
    pushout.inl (initial.to (interval x H)) (initial.to (base C)) ≫ sourceMap x (H := H) F =
      pushout.inl (initial.to (interval x H)) (initial.to (base D)) := by
  exact (pushout.inl_desc _ _ _).trans (Category.id_comp _)

/-- The actual source comparison retains the SAME whole original right pushout leg. -/
theorem sourceMap_right (F : C ⟶ D) :
    pushout.inr (initial.to (interval x H)) (initial.to (base C)) ≫ sourceMap x (H := H) F =
      LabelPushforward.map (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) F ≫
        pushout.inr (initial.to (interval x H)) (initial.to (base D)) :=
  pushout.inr_desc _ _ _

/-- The actual interval comparison retains the SAME whole original left pushout leg. -/
theorem intervalMap_left (G : H ⟶ K) :
    pushout.inl (initial.to (interval x H)) (initial.to (base C)) ≫ intervalMap x (C := C) G =
      LabelPushforward.map (FreeObjectPointPushout.labelMap x) G ≫
        pushout.inl (initial.to (interval x K)) (initial.to (base C)) :=
  pushout.inl_desc _ _ _

/-- The actual interval comparison retains the entire original right pushout leg. -/
theorem intervalMap_right (G : H ⟶ K) :
    pushout.inr (initial.to (interval x H)) (initial.to (base C)) ≫ intervalMap x (C := C) G =
      pushout.inr (initial.to (interval x K)) (initial.to (base C)) := by
  exact (pushout.inr_desc _ _ _).trans (Category.id_comp _)

/-- The SAME whole original interval map is unchanged under the actual source-row comparison. -/
theorem intervalLeg_sourceMap (F : C ⟶ D) :
    intervalLeg x C H ≫ (sourceMap x (H := H) F).val = intervalLeg x D H := by
  change (LabelPushforward.carrierUnit (FreeObjectPointPushout.labelMap x) H ≫ _ ) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => LabelPushforward.carrierUnit (FreeObjectPointPushout.labelMap x) H ≫ k)
      (congrArg (fun k => k.val) (sourceMap_left x (H := H) F)))

/-- The actual source-row comparison retains the SAME complete original source-functor square. -/
theorem sourceLeg_sourceMap (F : C ⟶ D) :
    sourceLeg x C H ≫ (sourceMap x (H := H) F).val = F.val ≫ sourceLeg x D H := by
  change (LabelPushforward.carrierUnit (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) C ≫ _) ≫ _ = _
  have h := congrArg (fun k => k.val) (sourceMap_right x (H := H) F)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => LabelPushforward.carrierUnit (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) C ≫ k)
      h).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (pushout.inr (initial.to (interval x H)) (initial.to (base D))).val)
          (LabelPushforward.carrierUnit_naturality (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) F)).trans
            (Category.assoc _ _ _))))

/-- The actual interval-row comparison retains the SAME complete original interval-functor square. -/
theorem intervalLeg_intervalMap (G : H ⟶ K) :
    intervalLeg x C H ≫ (intervalMap x (C := C) G).val = G.val ≫ intervalLeg x C K := by
  have h := congrArg (fun k => k.val) (intervalMap_left x (C := C) G)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => LabelPushforward.carrierUnit (FreeObjectPointPushout.labelMap x) H ≫ k) h).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (pushout.inl (initial.to (interval x K)) (initial.to (base C))).val)
          (LabelPushforward.carrierUnit_naturality (FreeObjectPointPushout.labelMap x) G)).trans
            (Category.assoc _ _ _))))

/-- The SAME entire original old-source map is unchanged under the actual interval-row comparison. -/
theorem sourceLeg_intervalMap (G : H ⟶ K) :
    sourceLeg x C H ≫ (intervalMap x (C := C) G).val = sourceLeg x C K :=
  (Category.assoc _ _ _).trans
    (congrArg (fun k => LabelPushforward.carrierUnit (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) C ≫ k)
      (congrArg (fun k => k.val) (intervalMap_right x (C := C) G)))

/-- The actual source and interval comparisons commute on the SAME entire original pushout maps. -/
theorem comparison_square (F : C ⟶ D) (G : H ⟶ K) :
    intervalMap x (C := C) G ≫ sourceMap x (H := K) F =
      sourceMap x (H := H) F ≫ intervalMap x (C := D) G := by
  apply pushout.hom_ext
  · rw [← Category.assoc, intervalMap_left, Category.assoc, sourceMap_left,
      ← Category.assoc, sourceMap_left, intervalMap_left]
  · rw [← Category.assoc, intervalMap_right, sourceMap_right,
      ← Category.assoc, sourceMap_right, Category.assoc, intervalMap_right]

end CategoryTheory.SimplicialEnrichment.IntervalPointPushoutRows
