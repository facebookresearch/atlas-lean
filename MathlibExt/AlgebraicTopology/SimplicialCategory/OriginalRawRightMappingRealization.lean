/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeRealization
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCubeMappingSpaceIso

/-!
# The full SAME raw right-mapping realization comparison

The actual full quotient-cube realization of every original
right-mapping space maps to the SAME raw coherent realization Hom.
The cocone retains every original coefficient and its full operators.
On the original coherent nerve its counit composite is the entire
original singular-complex evaluation.
-/

noncomputable section
universe u
open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping
open SimplicialEnrichment OriginalRightCubeRealization
variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The entire genuine original coefficient cocone into the SAME raw realization Hom. -/
def evaluationCocone : Cocone (OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b)) where
  pt := hom K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b)
  ι := {
    app e := cubeEvaluation a b e.unop.val
    naturality e d f := by
      have h := cubeEvaluation_operator a b f.unop.hom.unop d.unop.val
      exact h.trans ((congrArg (cubeEvaluation a b) f.unop.map_val).trans (Category.comp_id _).symm) }

/-- The SAME canonical full raw right-mapping comparison, obtained from every whole original coefficient. -/
def realizationComparison :
    OriginalRightCubeRealization.object (SSet.mappingSpaceRight K a b) ⟶
      hom K (SSet.yonedaEquiv a) (SSet.yonedaEquiv b) :=
  colimit.desc _ (evaluationCocone a b)

/-- Every whole original right-mapping simplex reads the SAME complete raw quotient-cube Hom evaluation. -/
theorem insertion_realizationComparison {n : ℕ} (σ : (SSet.mappingSpaceRight K a b) _⦋n⦌) :
    OriginalRightCubeRealization.insertion (SSet.mappingSpaceRight K a b)
      (op ((SSet.mappingSpaceRight K a b).elementsMk (op ⦋n⦌) σ)) ≫
        realizationComparison a b = cubeEvaluation a b σ :=
  colimit.ι_desc _ _

variable {C : Carrier.{u}} (x y : C)

/-- The original right-mapping coefficient cocone evaluates each entire cube to the SAME original Hom. -/
def counitEvaluationCocone :
    Cocone (OriginalRightCubeRealization.diagram
      (SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
        (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y))) where
  pt := x ⟶[SSet.{u}] y
  ι := {
    app e := (CubeMappingSpace.iso x y).hom.app e.unop.obj e.unop.val
    naturality e d f := by
      have h := CubeMappingNaturality.evaluate_naturality x y f.unop.hom.unop d.unop.val
      exact h.trans ((congrArg (FixedFrontMappingEvaluation.evaluate x y) f.unop.map_val).trans
        (Category.comp_id _).symm) }

/-- The SAME actual original singular-cube counit evaluation on the full original right-mapping realization. -/
def counitEvaluation :
    OriginalRightCubeRealization.object
      (SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
        (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)) ⟶ (x ⟶[SSet.{u}] y) :=
  colimit.desc _ (counitEvaluationCocone x y)

/-- The entire SAME original raw realization comparison followed by the original counit is precisely full original cube
evaluation. -/
theorem realizationComparison_counit :
    realizationComparison (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) ≫
      (counit C).map (SSet.yonedaEquiv (HomSimplexEndpoints.vertex x))
        (SSet.yonedaEquiv (HomSimplexEndpoints.vertex y)) =
      counitEvaluation x y := by
  apply colimit.hom_ext
  intro e
  change OriginalRightCubeRealization.insertion _ e ≫
      (realizationComparison (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y) ≫
        (counit C).map _ _) =
    OriginalRightCubeRealization.insertion _ e ≫ counitEvaluation x y
  have hInsert := colimit.ι_desc (evaluationCocone (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y)) e
  have hEval := colimit.ι_desc (counitEvaluationCocone x y) e
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (counit C).map _ _) hInsert).trans
      ((cubeEvaluation_counit x y e.unop.val).trans hEval.symm))

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
