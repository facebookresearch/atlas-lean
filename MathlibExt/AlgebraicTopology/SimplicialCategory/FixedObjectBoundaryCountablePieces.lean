/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectCountableCellTree
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeWeakSaturation
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.BoundedLowerSupport
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel

/-!
# Actual countable cofibrant pieces of the SAME original native boundary factor

The genuine original boundary-cell refinement supplies its actual
bounded lower supports. Each piece is literally its recorded lower
colimit under the original source. Its full maps recover the original
boundary left factor and supplied input. Genuine cell-tree weak
saturation proves the original piece inclusion cofibrant. Countability
is derived from actual original cells and predecessor colimits.
-/

noncomputable section
universe u
open CategoryTheory Limits SmallObject

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryGoodTree
variable {O : Type u} {C D : FixedObjects O} (f : C ⟶ D)

/-- The actual countable original lower supports on the SAME refined native occurrences. -/
abbrev Supports : Type u := @BoundedLowerSupport.Carrier (Cells f) (data f).order rank.{u}

/-- The SAME actual original lower-colimit point under its unchanged original source. -/
def piece (B : Supports f) : FixedObjects O := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact ((data f).lowerData.obj B.1).right

/-- The actual full original source inclusion into that SAME lower piece. -/
def root (B : Supports f) : C ⟶ piece f B := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact ((data f).lowerData.obj B.1).hom

/-- The whole original comparison into the SAME native boundary middle object. -/
def toMiddle (B : Supports f) : piece f B ⟶ (FreeFactorization.boundary f).Z := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact ((data f).lowerData.map (le_top : B.1 ≤ ⊤) ≫
    ((data f).tree.endpointIso (data f).lowerData).hom ≫ (data f).endpointIso.hom).right

/-- The SAME actual source and middle comparison recover the entire original boundary left factor. -/
theorem root_toMiddle (B : Supports f) : root f B ≫ toMiddle f B = (FreeFactorization.boundary f).i := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact Under.w ((data f).lowerData.map (le_top : B.1 ≤ ⊤) ≫
    ((data f).tree.endpointIso (data f).lowerData).hom ≫ (data f).endpointIso.hom)

/-- The full actual original map from the SAME countable piece to the unchanged supplied target. -/
def toOriginal (B : Supports f) : piece f B ⟶ D := toMiddle f B ≫ (FreeFactorization.boundary f).p

/-- Both actual whole original piece factors recover the SAME original input functor. -/
theorem root_toOriginal (B : Supports f) : root f B ≫ toOriginal f B = f := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (FreeFactorization.boundary f).p) (root_toMiddle f B)).trans
      (FreeFactorization.boundary_fac f))

/-- The actual source inclusion into every SAME original countable lower piece is genuinely fixed-model cofibrant. -/
theorem root_cofibration (B : Supports f) : FixedObjectModel.cofibrations O (root f B) := by
  let _ : PartialOrder (Cells f) := (data f).order
  let T := CellTreeLowerRestriction.tree (data f).tree (data f).lowerData B.1
  exact CellTreeWeakSaturation.hom_mem (boundaryFamily O).rlp.llp T T.lowerData
    (fun p => (boundaryFamily O).le_llp_rlp _ (T.label p).property)

/-- Every SAME original countable lower piece retains countable complete Homs on its unchanged original labels. -/
theorem piece_countableHoms [Countable O] [CountableHoms C] (B : Supports f) :
    CountableHoms (piece f B) := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact CountableCellTree.lower (data f).tree (data f).good
    (fun p => boundaryFamily_source_countable ((data f).tree.label p))
    (fun p => boundaryFamily_target_countable ((data f).tree.label p)) (data f).lowerData B.1 B.2

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryGoodTree
