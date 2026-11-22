/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontInsertion

/-!
# Whole enriched insertion readback of the actual resolving evaluation

For each supplied right-mapping simplex, the genuine resolving evaluation
recovers the entire original enriched successor simplex after the
distinguished insertion. This follows from the original quotient map and
the actual coherent nerve triangle, retaining every original Hom cell.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontEvaluationInsertion
open SimplicialEnrichment FixedFrontEvaluation
variable {C : Carrier.{u}} {n : ℕ} (x y : C)

/-- The actual quotient evaluation on the distinguished original successor simplex recovers the supplied
  whole enriched simplex. -/
theorem quotient_simplex
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    (quotientMap x y σ).app (op ⦋n + 1⦌) (FixedFrontInsertion.simplex n) =
      SSet.yonedaEquiv ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ).val := by
  exact congr($(quotientMap_readback x y σ).app (op ⦋n + 1⦌)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌)))

/-- The whole genuine resolving evaluation, after the distinguished insertion, retains every original
  supplied enriched object and Hom map. -/
theorem insertion
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    FixedFrontInsertion.functor n ≫ FixedFrontEvaluation.functor x y σ =
      SSet.yonedaEquiv ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ).val := by
  let τ := SSet.yonedaEquiv ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ).val
  have h := unit_simplex_naturality (quotientMap x y σ) (FixedFrontInsertion.simplex n)
  have ht : simplexInto (coherentNerveFunctor.obj C) τ ≫ counit C = τ :=
    congr($(nerve_triangle C).app (op ⦋n + 1⦌) τ)
  exact (Category.assoc (FixedFrontInsertion.functor n) (realizationMap (quotientMap x y σ)) (counit C)).symm.trans
    ((congrArg (fun F => F ≫ counit C) h).trans
      ((congrArg (fun z => simplexInto (coherentNerveFunctor.obj C) z ≫ counit C)
        (quotient_simplex x y σ)).trans ht))

end CategoryTheory.CoherentRealization.FixedFrontEvaluationInsertion
