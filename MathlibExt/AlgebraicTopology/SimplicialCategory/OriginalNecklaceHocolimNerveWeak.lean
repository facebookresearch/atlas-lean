/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceRawCoefficientContractible
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceHocolimRawAugmentation
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointFiberComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvarianceUniverses

/-!
# The SAME original native hocolim-to-input-nerve map is weak

Every original native raw endpoint Hom has its actual weak point
projection. Canonical Bousfield--Kan weak invariance and the original
point-diagram comparison prove weakness of the SAME full hocolim
projection to the nerve of its complete original native input category.
No quasicategory or desired comparison outcome is supplied.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

/-- The SAME original native hocolim-to-input-nerve projection using the full original raw coefficient diagram. -/
def hocolimNerveProjection (K : SSet.{u}) (x y : K _⦋0⦌) : hocolim K x y ⟶ nerve (Object K x y) :=
  SSet.bkHocolimToNerve (rawCoefficientDiagram K x y)

/-- The SAME actual full original native hocolim-to-input-nerve projection is weak for EVERY original simplicial
input. -/
theorem hocolimNerveProjection_weak (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.realizationWeakEquivalences (hocolimNerveProjection K x y) := by
  have h : SSet.realizationWeakEquivalences
      (SSet.bkHocolimMap (SSet.bkDiagramToPoint (rawCoefficientDiagram K x y))) :=
    SSet.bkHocolimMap_weak_universes _ (fun T => OriginalNecklaceHom.rawCoefficient_to_point_weak T.necklace)
  exact RespectsIso.postcomp SSet.realizationWeakEquivalences (SSet.bkPointIsoNerve (Object K x y)).hom
    (SSet.bkHocolimMap (SSet.bkDiagramToPoint (rawCoefficientDiagram K x y))) h

/-- The SAME original raw coherent Hom and complete native input-category nerve have the actual weak hocolim span. -/
theorem original_raw_nerve_weak_span (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.realizationWeakEquivalences (hocolimRawAugmentation K x y) ∧
      SSet.realizationWeakEquivalences (hocolimNerveProjection K x y) :=
  ⟨hocolimRawAugmentation_weak K x y, hocolimNerveProjection_weak K x y⟩

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
