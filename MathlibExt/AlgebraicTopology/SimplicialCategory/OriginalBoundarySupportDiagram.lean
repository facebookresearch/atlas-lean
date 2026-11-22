/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectBoundaryCountablePieces
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectOriginalFibrantReplacement
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.BoundedLowerSupport
import Mathlib.CategoryTheory.Presentable.Finite

/-!
# The actual original countable-support diagram and its full native endpoint

The SAME recorded countable lower pieces form their literal original
diagram under the original source. Its whole original endpoint is the
unchanged native boundary middle object. The original horn replacement
preserves this genuine filtered colimit. Every full original piece,
source map, endpoint leg and replacement map is retained.
-/

noncomputable section
universe u
open CategoryTheory Limits SmallObject

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundarySupportDiagram
open OriginalBoundaryGoodTree
variable {O : Type u} {C D : FixedObjects O} (f : C ⟶ D)

/-- The actual inherited order on the SAME original countable lower supports. -/
instance supportsOrder : PartialOrder (Supports f) := by
  let _ : PartialOrder (Cells f) := (data f).order
  infer_instance

/-- Genuine cardinal filteredness of the SAME original bounded-support category follows from actual unions. -/
instance supportsCardinalFiltered : IsCardinalFiltered (Supports f) rank.{u} := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact BoundedLowerSupport.cardinalFiltered rank

/-- The SAME original supports form an ordinary filtered category. -/
instance supportsFiltered : IsFiltered (Supports f) :=
  isFiltered_of_isCardinalFiltered (Supports f) rank

/-- The entire original endpoint presentation under its unchanged original source. -/
def underPresentation : ColimitPresentation (Supports f) (Under.mk (FreeFactorization.boundary f).i) := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact BoundedLowerSupport.endpointPresentation rank (data f).lowerData
    (data f).good.predecessor_lt
    ((data f).tree.endpointIso (data f).lowerData ≪≫ (data f).endpointIso)

/-- The literal SAME full original countable-piece diagram in the original fixed-label category. -/
def diagram : Supports f ⥤ FixedObjects O := (underPresentation f).diag ⋙ Under.forget C

/-- Every object of the whole original support diagram is literally the SAME recorded original piece. -/
theorem diagram_obj (B : Supports f) : (diagram f).obj B = piece f B := rfl

/-- The whole actual original cocone has the SAME original boundary middle object and full endpoint legs. -/
def cocone : Cocone (diagram f) := (Under.forget C).mapCocone (underPresentation f).cocone

/-- Every original full cocone leg is the SAME actual native-middle projection of its original piece. -/
theorem cocone_leg (B : Supports f) : (cocone f).ι.app B = toMiddle f B := by
  let _ : PartialOrder (Cells f) := (data f).order
  have h := BoundedLowerSupport.endpointPresentation_leg rank (data f).lowerData
    (data f).good.predecessor_lt
    ((data f).tree.endpointIso (data f).lowerData ≪≫ (data f).endpointIso) B
  exact congrArg Under.Hom.right h

/-- The SAME actual full native boundary middle object is the colimit of its original countable pieces. -/
def isColimit : IsColimit (cocone f) := by
  let _ : IsConnected (Supports f) := IsFiltered.isConnected (Supports f)
  let _ : HasColimit (underPresentation f).diag := (underPresentation f).hasColimit
  exact isColimitOfPreserves (Under.forget C) (underPresentation f).isColimit

/-- The genuine full original horn replacement of every SAME original countable piece. -/
abbrev replacedDiagram : Supports f ⥤ FixedObjects O := diagram f ⋙ OriginalFibrantReplacement.functor O

/-- The SAME actual original horn replacement of the native middle object receives the full original replaced cocone. -/
def replacedCocone : Cocone (replacedDiagram f) :=
  (OriginalFibrantReplacement.functor O).mapCocone (cocone f)

/-- Its actual full endpoint leg is the SAME original horn functor map of the original piece projection. -/
theorem replacedCocone_leg (B : Supports f) : (replacedCocone f).ι.app B =
    (OriginalFibrantReplacement.functor O).map (toMiddle f B) :=
  congrArg (OriginalFibrantReplacement.functor O).map (cocone_leg f B)

/-- The SAME original horn replacement preserves the full original countable-support endpoint colimit. -/
def replacedIsColimit : IsColimit (replacedCocone f) := by
  let _ : Fact Cardinal.aleph0.{u}.IsRegular := Cardinal.fact_isRegular_aleph0
  let _ : IsCardinalFiltered (Supports f) Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff (Supports f)).mpr inferInstance
  let _ : PreservesColimitsOfShape (Supports f) (OriginalFibrantReplacement.functor O) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible
      (OriginalFibrantReplacement.functor O) Cardinal.aleph0.{u} (Supports f)
  exact isColimitOfPreserves (OriginalFibrantReplacement.functor O) (isColimit f)

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundarySupportDiagram
