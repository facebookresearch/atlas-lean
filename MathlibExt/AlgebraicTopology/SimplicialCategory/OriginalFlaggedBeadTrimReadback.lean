/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedBeadOperator
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentRealizationMap

/-!
# The SAME actual full bead trim and raw component readback

The existing complete endpoint-interval Iso gives an actual original
flagged map from the trimmed original bead to that SAME original bead.
Its full input and coefficient equations retain every scalar simplex.
Thus the original raw generator maps to its original whole bead component.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead SimplicialEnrichment

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

private theorem trimBead_zero (b : Bead K x y q) :
    (trimOperator b.toArrow).toOrderHom 0 = 0 :=
  congrArg (fun i : coherentSimplex.{u} ⦋b.dimension⦌ => i.as.down) (trim_source b.toArrow)

private theorem trimBead_last (b : Bead K x y q) :
    (trimOperator b.toArrow).toOrderHom (Fin.last (trimDimension b.toArrow)) = Fin.last b.dimension :=
  congrArg (fun i : coherentSimplex.{u} ⦋b.dimension⦌ => i.as.down) (trim_target b.toArrow)

/-- The SAME entire original full-bead trim coefficient is recovered by its actual original interval map. -/
theorem trimBead_coefficient (b : Bead K x y q) :
    (OriginalBead.OuterOperator.map (trimOperator b.toArrow) (trimBead_zero b) (trimBead_last b)).app q
      (trim b.toArrow).coefficient = b.coefficient := by
  have hM : OriginalBead.OuterOperator.map (trimOperator b.toArrow) (trimBead_zero b) (trimBead_last b) =
      (trimHomIso b.toArrow).hom :=
    (OriginalBead.OuterOperator.map_coherent _ _ _).trans (trimHomIso_hom b.toArrow).symm
  have h := ConcreteCategory.congr_hom (congr_app (trimHomIso b.toArrow).inv_hom_id q) b.coefficient
  exact (congrArg (fun f => f.app q (trim b.toArrow).coefficient) hM).trans h

/-- The actual original flagged map from the complete endpoint trim to the SAME original full bead. -/
def trimBeadMap (b : Bead K x y q) : ofBead (trim b.toArrow) ⟶ ofBead b :=
  beadOperator (trim b.toArrow) b (trimOperator b.toArrow) (trimBead_zero b) (trimBead_last b)
    rfl (trimBead_coefficient b)

/-- Both SAME full original beads have their literal original component equality. -/
theorem trimBead_component (b : Bead K x y q) :
    CategoryTheory.ConnectedComponents.mk (ofBead (trim b.toArrow)) =
      CategoryTheory.ConnectedComponents.mk (ofBead b) :=
  _root_.Quotient.sound (Zigzag.of_hom (trimBeadMap b))

namespace Components

/-- EVERY original raw full-bead generator maps to its SAME entire original flagged bead component. -/
theorem rawHomMap_bead (b : Bead K x y q) :
    (rawHomMap K x y).app q b.evaluation = CategoryTheory.ConnectedComponents.mk (ofBead b) :=
  (rawHomMap_arrow b.toArrow).trans (trimBead_component b)

end Components

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
