/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalLabelPushforwardGlobalPushout
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalTwoLabelUnitGroupoid

/-!
# The actual free-object point pushout adds exactly the original new label

The SAME initial enrichments on the original object families give a
genuine full carrier pushout. The selected old label is retained and
the other original two-label vertex becomes the actual new label. Both
complete object functions and every original full map are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FreeObjectPointPushout
open FixedObjects

variable {O : Type u} (x : O)

/-- The exact original object family with one actual new label. -/
abbrev labels : Type u := O ⊕ PUnit.{u+1}

/-- The SAME two original labels map to the selected old label and the actual new one. -/
def labelMap : OriginalTwoLabelUnitGroupoid.labels.{u} → labels (O := O)
  | ⟨.source⟩ => Sum.inl x
  | ⟨.target⟩ => Sum.inr PUnit.unit

/-- The selected original source label maps to precisely the SAME old label. -/
theorem labelMap_source : labelMap x OriginalTwoLabelUnitGroupoid.source = Sum.inl x := rfl

/-- The actual original target label maps to precisely the SAME new label. -/
theorem labelMap_target : labelMap x OriginalTwoLabelUnitGroupoid.target = Sum.inr PUnit.unit := rfl

/-- The actual two original labels remain distinct under the SAME prescribed map. -/
theorem labelMap_injective : Function.Injective (labelMap x) := by
  intro s t h
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  cases s <;> cases t
  case source.source => rfl
  case target.target => rfl
  case source.target => cases h
  case target.source => cases h

/-- The SAME original source point in the actual two-label initial enrichment. -/
def leftPoint : BergnerObjects.point.{u} ⟶ BergnerFixedInitialObjects.object OriginalTwoLabelUnitGroupoid.labels.{u} :=
  BergnerObjects.select (C := BergnerFixedInitialObjects.object OriginalTwoLabelUnitGroupoid.labels.{u})
    (BergnerFixedInitialObjects.vertex OriginalTwoLabelUnitGroupoid.labels.{u} OriginalTwoLabelUnitGroupoid.source)

/-- The SAME selected original point in the actual old-label initial enrichment. -/
def rightPoint : BergnerObjects.point.{u} ⟶ BergnerFixedInitialObjects.object O :=
  BergnerObjects.select (C := BergnerFixedInitialObjects.object O) (BergnerFixedInitialObjects.vertex O x)

/-- The entire original two-label free map on its SAME prescribed old and new images. -/
def upper : BergnerFixedInitialObjects.object OriginalTwoLabelUnitGroupoid.labels.{u} ⟶
    BergnerFixedInitialObjects.object (labels (O := O)) :=
  LabelPushforward.GlobalPushout.labelsMap (labelMap x)

/-- The complete original old-label free inclusion. -/
def lower : BergnerFixedInitialObjects.object O ⟶ BergnerFixedInitialObjects.object (labels (O := O)) :=
  LabelPushforward.GlobalPushout.labelsMap (Sum.inl : O → labels (O := O))

/-- Both SAME full original point maps commute in the actual free-object square. -/
theorem condition : leftPoint.{u} ≫ upper x = rightPoint x ≫ lower (O := O) := by
  have hl : leftPoint.{u} ≫ upper x =
      BergnerObjects.select (C := BergnerFixedInitialObjects.object (labels (O := O)))
        (BergnerFixedInitialObjects.vertex (labels (O := O)) (Sum.inl x)) :=
    (BergnerObjects.select_comp
      (BergnerFixedInitialObjects.vertex OriginalTwoLabelUnitGroupoid.labels.{u} OriginalTwoLabelUnitGroupoid.source)
        (upper x)).trans
      (congrArg (BergnerObjects.select (C := BergnerFixedInitialObjects.object (labels (O := O))))
        (BergnerFixedInitialObjects.desc_vertex OriginalTwoLabelUnitGroupoid.labels.{u}
          (fun t => BergnerFixedInitialObjects.vertex (labels (O := O)) (labelMap x t))
            OriginalTwoLabelUnitGroupoid.source))
  have hr : rightPoint x ≫ lower (O := O) =
      BergnerObjects.select (C := BergnerFixedInitialObjects.object (labels (O := O)))
        (BergnerFixedInitialObjects.vertex (labels (O := O)) (Sum.inl x)) :=
    (BergnerObjects.select_comp (BergnerFixedInitialObjects.vertex O x) (lower (O := O))).trans
      (congrArg (BergnerObjects.select (C := BergnerFixedInitialObjects.object (labels (O := O))))
        (BergnerFixedInitialObjects.desc_vertex O
          (fun o => BergnerFixedInitialObjects.vertex (labels (O := O)) (Sum.inl o)) x))
  exact hl.trans hr.symm

/-- The actual original free-object point cocone. -/
def cocone : PushoutCocone leftPoint.{u} (rightPoint x) := PushoutCocone.mk (upper x) (lower (O := O)) (condition x)

variable (s : PushoutCocone leftPoint.{u} (rightPoint x))

/-- The SAME complete original cocone forces its actual selected-source equality. -/
theorem source_eq : s.inl.obj (BergnerFixedInitialObjects.vertex OriginalTwoLabelUnitGroupoid.labels.{u}
    OriginalTwoLabelUnitGroupoid.source) = s.inr.obj (BergnerFixedInitialObjects.vertex O x) :=
  congrArg (fun F : BergnerObjects.point.{u} ⟶ s.pt => F.obj PUnit.unit) s.condition

/-- Read the exact original old objects and actual new target object from the SAME supplied cocone. -/
def objectMap : labels (O := O) → s.pt :=
  Sum.elim (fun o => s.inr.obj (BergnerFixedInitialObjects.vertex O o))
    (fun _ => s.inl.obj (BergnerFixedInitialObjects.vertex OriginalTwoLabelUnitGroupoid.labels.{u}
      OriginalTwoLabelUnitGroupoid.target))

/-- The genuine original initial-enrichment descender on precisely those SAME object images. -/
def desc : BergnerFixedInitialObjects.object (labels (O := O)) ⟶ s.pt :=
  BergnerFixedInitialObjects.desc (labels (O := O)) (objectMap x s)

/-- Every complete original two-label cocone map is recovered by the SAME descender. -/
theorem desc_left : upper x ≫ desc x s = s.inl := by
  apply (BergnerFixedInitialObjects.homEquiv OriginalTwoLabelUnitGroupoid.labels.{u} s.pt).injective
  funext t
  have h₁ := congrArg (desc x s).obj
    (BergnerFixedInitialObjects.desc_vertex OriginalTwoLabelUnitGroupoid.labels.{u}
      (fun t => BergnerFixedInitialObjects.vertex (labels (O := O)) (labelMap x t)) t)
  have h₂ := BergnerFixedInitialObjects.desc_vertex (labels (O := O)) (objectMap x s) (labelMap x t)
  have h₃ : objectMap x s (labelMap x t) = s.inl.obj (BergnerFixedInitialObjects.vertex
      OriginalTwoLabelUnitGroupoid.labels.{u} t) := by
    rcases t with ⟨t⟩
    cases t
    case source => exact (source_eq x s).symm
    case target => rfl
  exact h₁.trans (h₂.trans h₃)

/-- Every whole original old-label cocone map is recovered by the SAME descender. -/
theorem desc_right : lower (O := O) ≫ desc x s = s.inr := by
  apply (BergnerFixedInitialObjects.homEquiv O s.pt).injective
  funext o
  exact (congrArg (desc x s).obj (BergnerFixedInitialObjects.desc_vertex O
    (fun o => BergnerFixedInitialObjects.vertex (labels (O := O)) (Sum.inl o)) o)).trans
      (BergnerFixedInitialObjects.desc_vertex (labels (O := O)) (objectMap x s) (Sum.inl o))

/-- The actual entire old-label leg fixes every SAME original old image. -/
theorem old_readback (H : BergnerFixedInitialObjects.object (labels (O := O)) ⟶ s.pt)
    (h : lower (O := O) ≫ H = s.inr) (o : O) :
    H.obj (BergnerFixedInitialObjects.vertex (labels (O := O)) (Sum.inl o)) =
      objectMap x s (Sum.inl o) := by
  have he := congrArg (fun F : BergnerFixedInitialObjects.object O ⟶ s.pt =>
    F.obj (BergnerFixedInitialObjects.vertex O o)) h
  exact (congrArg H.obj (BergnerFixedInitialObjects.desc_vertex O
    (fun o => BergnerFixedInitialObjects.vertex (labels (O := O)) (Sum.inl o)) o)).symm.trans he

/-- The actual entire two-label leg fixes the SAME original new target image. -/
theorem new_readback (H : BergnerFixedInitialObjects.object (labels (O := O)) ⟶ s.pt)
    (h : upper x ≫ H = s.inl) :
    H.obj (BergnerFixedInitialObjects.vertex (labels (O := O)) (Sum.inr PUnit.unit)) =
      objectMap x s (Sum.inr PUnit.unit) := by
  have he := congrArg (fun F : BergnerFixedInitialObjects.object OriginalTwoLabelUnitGroupoid.labels.{u} ⟶ s.pt =>
    F.obj (BergnerFixedInitialObjects.vertex OriginalTwoLabelUnitGroupoid.labels.{u}
      OriginalTwoLabelUnitGroupoid.target)) h
  exact (congrArg H.obj (BergnerFixedInitialObjects.desc_vertex OriginalTwoLabelUnitGroupoid.labels.{u}
    (fun t => BergnerFixedInitialObjects.vertex (labels (O := O)) (labelMap x t))
      OriginalTwoLabelUnitGroupoid.target)).symm.trans he

/-- Both SAME complete original legs determine the genuine full enriched extension. -/
theorem desc_unique (H : BergnerFixedInitialObjects.object (labels (O := O)) ⟶ s.pt)
    (hl : upper x ≫ H = s.inl) (hr : lower (O := O) ≫ H = s.inr) : H = desc x s := by
  apply (BergnerFixedInitialObjects.homEquiv (labels (O := O)) s.pt).injective
  funext o
  cases o with
  | inl o =>
      exact (old_readback x s H hr o).trans
        (BergnerFixedInitialObjects.desc_vertex (labels (O := O)) (objectMap x s) (Sum.inl o)).symm
  | inr o =>
      cases o
      exact (new_readback x s H hl).trans
        (BergnerFixedInitialObjects.desc_vertex (labels (O := O)) (objectMap x s) (Sum.inr PUnit.unit)).symm

/-- The actual full original point cocone has its genuine changing-object enriched universal property. -/
def isColimit : IsColimit (cocone x) :=
  PushoutCocone.IsColimit.mk (condition x) (desc x) (desc_left x) (desc_right x) (desc_unique x)

/-- The SAME whole free-object square is an actual original global enriched pushout. -/
theorem isPushout : IsPushout leftPoint.{u} (rightPoint x) (upper x) (lower (O := O)) :=
  IsPushout.of_isColimit (isColimit x)

end CategoryTheory.SimplicialEnrichment.FreeObjectPointPushout
