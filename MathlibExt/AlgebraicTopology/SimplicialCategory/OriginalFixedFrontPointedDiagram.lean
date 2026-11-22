/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontAugmentationWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontVertices
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryOneMapNaturality
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The SAME full fixed-front cosimplicial diagram with both original endpoints

Every original quotient and operator is retained in Under(∂Δ[1]).
The original source and target vertex readbacks prove its literal
boundary equations. This constructs the genuine pointed diagram,
without assuming Reedy cofibrancy or a resolution outcome.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The SAME actual fixed-front quotient with its two original structural endpoint maps. -/
def pointedObject (n : ℕ) : Under (∂Δ[1] : SSet.{u}) :=
  Under.mk (SSet.boundaryOneMap (FixedFrontCollapse.source n) (FixedFrontCollapse.target n))

/-- Every SAME original quotient operator retains both complete original boundary endpoint equations. -/
theorem pointedMap_boundary {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    (pointedObject.{u} n).hom ≫ FixedFrontOperators.map θ = (pointedObject m).hom :=
  (SSet.boundaryOneMap_naturality (FixedFrontOperators.map θ)
    (FixedFrontCollapse.source n) (FixedFrontCollapse.target n)).trans
      (congrArg₂ SSet.boundaryOneMap (FixedFrontVertices.map_source θ) (FixedFrontVertices.map_target θ))

/-- The SAME full original pointed cosimplicial operator, retaining its literal underlying quotient map. -/
def pointedMap {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌) : pointedObject.{u} n ⟶ pointedObject m :=
  Under.homMk (FixedFrontOperators.map θ) (pointedMap_boundary θ)

/-- The genuine SAME fixed-front cosimplicial diagram in the endpoint-fixed category. -/
def pointedCosimplicialObject : CosimplicialObject (Under (∂Δ[1] : SSet.{u})) where
  obj n := pointedObject n.len
  map θ := pointedMap θ
  map_id n := Under.UnderMorphism.ext (FixedFrontOperators.map_id n.len)
  map_comp θ ψ := Under.UnderMorphism.ext (FixedFrontOperators.map_comp θ ψ)

/-- Every original pointed operator keeps the SAME full underlying fixed-front quotient map. -/
theorem pointedMap_right {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    (pointedMap.{u} θ).right = FixedFrontOperators.map θ := rfl

/-- The SAME original endpoint-fixed diagram retains the whole underlying original cosimplicial diagram. -/
theorem pointedCosimplicialObject_forget :
    pointedCosimplicialObject.{u} ⋙ Under.forget (∂Δ[1] : SSet.{u}) = cosimplicialObject.{u} := rfl

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
