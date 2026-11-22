/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFreeObjectPointPushout
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectGlobalPushout

/-!
# The actual original interval point pushout is the SAME full fixed-label frame

Both genuine original label-pushforward squares and the actual free
object point square paste with the supplied fixed-object pushout.
The entire resulting carrier square has the original interval point,
original selected source object and SAME full original source maps.
No global model or weak-comparison outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.IntervalPointPushoutFrame
open FixedObjects

variable {O : Type u} (x : O) (C : FixedObjects O)
  (H : FixedObjects OriginalTwoLabelUnitGroupoid.labels.{u})

/-- The SAME original interval extended onto the old labels and the actual new label. -/
abbrev interval : FixedObjects (FreeObjectPointPushout.labels (O := O)) :=
  LabelPushforward.object (FreeObjectPointPushout.labelMap x) H

/-- The SAME full original source with its actual unused new label. -/
abbrev base : FixedObjects (FreeObjectPointPushout.labels (O := O)) :=
  LabelPushforward.object (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) C

/-- The complete original interval leg retains each SAME original injected vertex. -/
theorem intervalLeg_vertex {P : FixedObjects (FreeObjectPointPushout.labels (O := O))}
    (j : interval x H ⟶ P) (s : OriginalTwoLabelUnitGroupoid.labels.{u}) :
    (LabelPushforward.carrierUnit (FreeObjectPointPushout.labelMap x) H ≫ j.val).obj (vertex H s) =
      vertex P (FreeObjectPointPushout.labelMap x s) :=
  (congrArg j.val.obj (LabelPushforward.carrierUnit_vertex (FreeObjectPointPushout.labelMap x) H s)).trans
    (map_vertex j (FreeObjectPointPushout.labelMap x s))

/-- The complete original source leg retains every SAME original old vertex. -/
theorem baseLeg_vertex {P : FixedObjects (FreeObjectPointPushout.labels (O := O))}
    (k : base C ⟶ P) (o : O) :
    (LabelPushforward.carrierUnit (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) C ≫ k.val).obj
      (vertex C o) = vertex P (Sum.inl o) :=
  (congrArg k.val.obj (LabelPushforward.carrierUnit_vertex
    (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) C o)).trans (map_vertex k (Sum.inl o))

/-- The SAME original full fixed-label frame has the genuine original varying-object point-pushout property. -/
theorem isPushout {P : FixedObjects (FreeObjectPointPushout.labels (O := O))}
    {j : interval x H ⟶ P} {k : base C ⟶ P}
    (sq : IsPushout (initial.to (interval x H)) (initial.to (base C)) j k) :
    IsPushout
      (BergnerObjects.select (C := H.val) (vertex H OriginalTwoLabelUnitGroupoid.source))
      (BergnerObjects.select (C := C.val) (vertex C x))
      (LabelPushforward.carrierUnit (FreeObjectPointPushout.labelMap x) H ≫ j.val)
      (LabelPushforward.carrierUnit (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) C ≫ k.val) := by
  have leftColumn := (FreeObjectPointPushout.isPushout x).paste_vert
    (LabelPushforward.GlobalPushout.isPushout (Sum.inl : O → FreeObjectPointPushout.labels (O := O)) C).flip
  have rightColumn := (LabelPushforward.GlobalPushout.isPushout (FreeObjectPointPushout.labelMap x) H).paste_vert
    (FixedObjects.GlobalPushout.isPushout sq)
  have outer := leftColumn.paste_horiz rightColumn
  have hl : FreeObjectPointPushout.leftPoint.{u} ≫ LabelPushforward.GlobalPushout.sourceMap H =
      BergnerObjects.select (C := H.val) (vertex H OriginalTwoLabelUnitGroupoid.source) :=
    (BergnerObjects.select_comp
      (BergnerFixedInitialObjects.vertex OriginalTwoLabelUnitGroupoid.labels.{u} OriginalTwoLabelUnitGroupoid.source)
      (LabelPushforward.GlobalPushout.sourceMap H)).trans
        (congrArg (BergnerObjects.select (C := H.val))
          (map_vertex (initial.to H) OriginalTwoLabelUnitGroupoid.source))
  have hr : FreeObjectPointPushout.rightPoint x ≫ LabelPushforward.GlobalPushout.sourceMap C =
      BergnerObjects.select (C := C.val) (vertex C x) :=
    (BergnerObjects.select_comp (BergnerFixedInitialObjects.vertex O x)
      (LabelPushforward.GlobalPushout.sourceMap C)).trans
        (congrArg (BergnerObjects.select (C := C.val)) (map_vertex (initial.to C) x))
  exact hl ▸ hr ▸ outer

end CategoryTheory.SimplicialEnrichment.IntervalPointPushoutFrame
