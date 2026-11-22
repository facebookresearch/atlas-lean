/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedGadgetInputs
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalReedyGadgetHomPoint

/-!
# The actual original Reedy diagram in the full fibrant gadget category

Every same generated Reedy degree is a genuinely fibrant mapping gadget.
All original operators use the same full generated maps and complete
pointed boundaries. The original source functor and actual input map
retain the whole Hom-simplex indexing category.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The same entire original generated Reedy diagram in its genuinely fibrant full mapping-gadget category. -/
def fibrantReedyGadgetDiagram : CosimplicialObject OriginalPointed.FibrantMappingGadgets.{u} where
  obj n := ⟨⟨rawReedyDegree n, OriginalPointed.reedyDegree_mappingGadget n⟩, reedyReplacement_raw_quasicategory n⟩
  map θ := ObjectProperty.homMk (ObjectProperty.homMk (pointedRawFunctor.map (reedyReplacement.map θ)))
  map_id n := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (congrArg pointedRawFunctor.map (reedyReplacement.map_id n)).trans
      (pointedRawFunctor.map_id _)
  map_comp θ ψ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (congrArg pointedRawFunctor.map (reedyReplacement.map_comp θ ψ)).trans
      (pointedRawFunctor.map_comp _ _)

/-- The whole original fibrant-gadget Reedy diagram forgets to the exact original full pointed Reedy diagram. -/
theorem fibrantReedyGadgetDiagram_forget :
    fibrantReedyGadgetDiagram.{u} ⋙ OriginalPointed.fibrantGadgetFullInclusion =
      reedyReplacement ⋙ pointedRawFunctor := rfl

/-- The actual full original Reedy-input functor into the same original full fibrant-gadget input category. -/
def reedyIntoFibrantGadgetInputs (K : OriginalPointed.Category.{u}) :
    CostructuredArrow (reedyReplacement ⋙ pointedRawFunctor) K ⥤
      CostructuredArrow OriginalPointed.fibrantGadgetFullInclusion K :=
  CostructuredArrow.pre fibrantReedyGadgetDiagram OriginalPointed.fibrantGadgetFullInclusion K

/-- The same entire original Reedy-input comma retains every original generated Hom map. -/
def reedyFibrantCommaEquivalence (K : OriginalPointed.Category.{u})
    (Y : CostructuredArrow OriginalPointed.fibrantGadgetFullInclusion K) :
    CostructuredArrow (reedyIntoFibrantGadgetInputs K) Y ≌ CostructuredArrow fibrantReedyGadgetDiagram Y.left :=
  CostructuredArrow.preEquivalence fibrantReedyGadgetDiagram Y

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
