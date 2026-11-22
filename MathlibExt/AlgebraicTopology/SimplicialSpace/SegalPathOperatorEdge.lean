/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathOperatorTriangleMap

/-!
# The actual original operator edge as a prescribed-endpoint mapping-fibre point

The operator's initial edge runs from the first vertex of the original
tail simplex to the first vertex of its original reindexing. Both
endpoints are derived from those full original maps. This supplies
the actual mapping-fibre point used for the Segal composition action.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The actual original operator edge as a map on the entire original zero simplex. -/
def operatorEdgeMap {m n : ℕ} (W : SimplicialSpace.{u})
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋1⦌ :=
  b ≫ W.diagram.map (operatorInitialEdge f).op

/-- The whole original operator edge retains the actual first vertex of its full source tail. -/
theorem operatorEdgeMap_source {m n : ℕ} (W : SimplicialSpace.{u})
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    operatorEdgeMap W f b ≫ W.diagram.δ (1 : Fin 2) =
      SSet.yonedaEquiv.symm (tailFirstPoint W n b) := by
  unfold operatorEdgeMap
  simp only [Category.assoc, SimplicialObject.δ]
  rw [← W.diagram.map_comp, ← op_comp]
  have he : SimplexCategory.δ (1 : Fin 2) ≫ operatorInitialEdge f =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) 0 := by
    ext i
    fin_cases i
    rfl
  rw [he]
  simp only [tailFirstPoint, InitialEdgeTailMapping.tailFirstVertex, Equiv.symm_apply_apply]

/-- The whole original operator edge retains the actual first vertex after reindexing its full target tail. -/
theorem operatorEdgeMap_target {m n : ℕ} (W : SimplicialSpace.{u})
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    operatorEdgeMap W f b ≫ W.diagram.δ (0 : Fin 2) =
      SSet.yonedaEquiv.symm (tailFirstPoint W m (b ≫ W.diagram.map f.op)) := by
  unfold operatorEdgeMap
  simp only [Category.assoc, SimplicialObject.δ, tailFirstPoint,
    InitialEdgeTailMapping.tailFirstVertex, Equiv.symm_apply_apply]
  rw [← W.diagram.map_comp, ← W.diagram.map_comp, ← op_comp, ← op_comp]
  have he : SimplexCategory.δ (0 : Fin 2) ≫ operatorInitialEdge f =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m) 0 ≫ f := by
    ext i
    fin_cases i
    rfl
  rw [he]

/-- The actual original operator edge is a genuine mapping-fibre point at its same original endpoints. -/
def operatorEdgeFibreMap {m n : ℕ} (W : SimplicialSpace.{u})
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    (Δ[0] : SSet.{u}) ⟶ mappingFibre W (tailFirstPoint W n b)
      (tailFirstPoint W m (b ≫ W.diagram.map f.op)) :=
  pullback.lift (operatorEdgeMap W f b) (𝟙 _) (by
    apply prod.hom_ext
    · simpa only [Category.assoc, mappingEndpoint_fst, mappingPointPair_fst, Category.id_comp] using
        operatorEdgeMap_source W f b
    · simpa only [Category.assoc, mappingEndpoint_snd, mappingPointPair_snd, Category.id_comp] using
        operatorEdgeMap_target W f b)

/-- The whole actual operator mapping-fibre point retains the original edge map. -/
theorem operatorEdgeFibreMap_fst {m n : ℕ} (W : SimplicialSpace.{u})
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    operatorEdgeFibreMap W f b ≫ mappingFibre.fst W (tailFirstPoint W n b)
      (tailFirstPoint W m (b ≫ W.diagram.map f.op)) = operatorEdgeMap W f b :=
  pullback.lift_fst _ _ _

end SimplicialSpace.LeftDecalageObject
