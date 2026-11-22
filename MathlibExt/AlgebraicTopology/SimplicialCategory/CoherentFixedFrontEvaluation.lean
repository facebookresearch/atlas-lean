/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontUniversalMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightMappingSimplex
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCounit

/-!
# Actual original evaluation of the fixed-front right resolution

Every supplied original right-mapping simplex factors through the
constructed fixed-front resolving quotient. Its actual realization and
counit give a genuine enriched functor to the original target, retaining
its individual source/target vertex images. No Hom-identification or
weak-resolution outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontEvaluation
open SimplicialEnrichment FixedFrontCollapse FixedFrontUniversalMap
variable {C : Carrier.{u}} {n : ℕ} (x y : C)

/-- The actual whole fixed-front quotient map carried by a supplied original right-mapping simplex. -/
def quotientMap (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    FixedFrontCollapse.object.{u} n ⟶ coherentNerveFunctor.obj C :=
  lift ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ).val (HomSimplexEndpoints.vertex x)
    ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ).2.1

/-- The actual resolving quotient map reads back the entire supplied original successor simplex. -/
theorem quotientMap_readback
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    FixedFrontCollapse.projection n ≫ quotientMap x y σ = ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ).val :=
  projection_lift _ _ _

/-- The actual enriched evaluation functor from the constructed resolving quotient realization to the
  original target. -/
def functor (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    realization (FixedFrontCollapse.object.{u} n) ⟶ C :=
  realizationMap (quotientMap x y σ) ≫ counit C

/-- The genuine enriched evaluation retains the actual original object read by its resolving quotient vertex map. -/
theorem functor_obj
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌)
    (a : (FixedFrontCollapse.object.{u} n) _⦋0⦌) :
    (functor x y σ).obj a = vertexOf C ((quotientMap x y σ).app (op ⦋0⦌) a) := rfl

/-- The actual enriched evaluation reads the specified original source object at the structural source vertex. -/
theorem functor_source
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    (functor x y σ).obj (FixedFrontCollapse.source n) = x := by
  let t := (SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ
  have hY : t.val.app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0)) =
    (coherentNerveFunctor.obj C).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (SSet.yonedaEquiv t.val) := by
    exact congrArg (fun f => f.app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0)))
        (SSet.yonedaEquiv.symm_apply_apply t.val).symm
  have hO := congrArg (vertexOf C) hY
  exact hO.trans (RightMappingSimplex.front_obj x y σ (0 : Fin (n + 1)))

/-- The actual enriched evaluation reads the specified original target object at the original structural last vertex. -/
theorem functor_target
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    (functor x y σ).obj (FixedFrontCollapse.target n) = y := by
  let t := (SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) σ
  have hY : t.val.app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)))) =
    (coherentNerveFunctor.obj C).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))).op
      (SSet.yonedaEquiv t.val) := by
    exact congrArg (fun f => f.app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)))))
        (SSet.yonedaEquiv.symm_apply_apply t.val).symm
  have hO := congrArg (vertexOf C) hY
  exact hO.trans (RightMappingSimplex.last_obj x y σ)

/-- The whole actual evaluation map on the original source-to-target resolving Hom. -/
def homMap
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    FixedFrontCollapse.rightHom.{u} n ⟶ (x ⟶[SSet.{u}] y) :=
  (functor x y σ).map (FixedFrontCollapse.source n) (FixedFrontCollapse.target n) ≫
    eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) (functor_source x y σ) (functor_target x y σ))

end CategoryTheory.CoherentRealization.FixedFrontEvaluation
