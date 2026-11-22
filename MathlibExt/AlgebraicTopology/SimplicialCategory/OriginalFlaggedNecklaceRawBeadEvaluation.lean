/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceRawEvaluationScalar
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentSimplexInsertion

/-!
# The SAME actual original whole-bead evaluation

The full native bead ambient functor followed by the original simplex
insertion is the SAME realized entire input map. The original raw Hom
and native coefficient readbacks therefore evaluate a full flagged bead
as its original coherent generator, with every input and flag retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalNecklaceHom OriginalBead SimplicialEnrichment

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME whole native bead ambient and insertion functors retain its entire original input. -/
theorem ambientFunctor_bead_input (b : Bead K x y q) :
    ambientFunctor.{u} (beadData b.dimension) ≫ simplexInto K b.simplex = realizationMap (ofBead b).input := by
  change (realizationMap (beadChart.{u} b.dimension).hom ≫ (simplexIso.{u} ⦋b.dimension⦌).hom) ≫
    simplexInto K b.simplex = realizationMap ((beadChart b.dimension).hom ≫ SSet.yonedaEquiv.symm b.simplex)
  rw [realizationMap_comp, Category.assoc, simplexIso_hom_insertion]

/-- The SAME entire native bead coefficient and original raw insertion have the literal input Hom square. -/
theorem ambientHomMap_bead_input (b : Bead K x y q) :
    ambientHomMap.{u} (beadData b.dimension) ≫
      simplexHom K b.simplex (initial.{u} b.dimension) (terminal.{u} b.dimension) b.source_eq b.target_eq =
        inputHomMap (ofBead b) := by
  have hP : EnrichedFunctor.homMap (simplexInto K b.simplex) b.source_eq b.target_eq =
      simplexHom K b.simplex (initial.{u} b.dimension) (terminal.{u} b.dimension) b.source_eq b.target_eq :=
    simplexHom_reindex_comp K b.simplex (initial.{u} b.dimension) (terminal.{u} b.dimension)
      rfl rfl b.source_eq b.target_eq
  have hL := EnrichedFunctor.homMap_comp (ambientFunctor (beadData b.dimension))
    (simplexInto K b.simplex) (ambientFunctor_source (beadData b.dimension))
      (ambientFunctor_target (beadData b.dimension)) b.source_eq b.target_eq
  have hE := EnrichedFunctor.homMap_eq (ambientFunctor_bead_input b)
    ((congrArg (simplexInto K b.simplex).obj (ambientFunctor_source (beadData b.dimension))).trans b.source_eq)
    ((congrArg (simplexInto K b.simplex).obj (ambientFunctor_target (beadData b.dimension))).trans b.target_eq)
    (input_source (ofBead b)) (input_target (ofBead b))
  exact (congrArg (fun e => ambientHomMap (beadData b.dimension) ≫ e) hP).symm.trans (hL.trans hE)

/-- EVERY SAME full original flagged bead evaluates to its original raw coherent Hom generator. -/
theorem evaluation_ofBead (b : Bead K x y q) : evaluation (ofBead b) = b.evaluation := by
  have h := ConcreteCategory.congr_hom (congr_app (ambientHomMap_bead_input b) q)
    (coefficientLift (beadData b.dimension) (jointCoefficient (ofBead b)))
  exact h.symm.trans (congrArg
    ((simplexHom K b.simplex (initial.{u} b.dimension) (terminal.{u} b.dimension) b.source_eq b.target_eq).app q)
    (coefficientLift_ambient (beadData b.dimension) (jointCoefficient (ofBead b))))

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
