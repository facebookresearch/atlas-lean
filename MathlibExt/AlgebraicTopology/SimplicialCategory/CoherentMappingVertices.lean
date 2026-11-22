/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedEdgeReadback

/-!
# Individual original vertices of the coherent right mapping space

Every actual right-mapping-space vertex has its supplied original object
endpoints and its exact original enriched Hom vertex. The genuine
comparison and this readback are inverse on individual vertices. No
component quotient of objects or higher simplicial inverse is asserted.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingVertices
open SimplicialEnrichment HomSimplexEndpoints HomMapping HomMappingCells
variable {C : Carrier.{u}} (x y : C)

/-- The actual enriched coherent edge carried by the supplied original right-mapping vertex. -/
def enrichedEdge (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋0⦌) :
    coherentSimplex.{u} ⦋1⦌ ⟶ C :=
  SSet.yonedaEquiv ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ 0) σ).val

/-- The actual enriched edge starts at the supplied individual original source object. -/
theorem source (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋0⦌) :
    (enrichedEdge x y σ).obj (.mk (ULift.up (0 : Fin 2))) = x := by
  let t := (SSet.mappingSpaceRight.simplexEquivSucc _ _ _ 0) σ
  have hT : SSet.toDeltaZero (Δ[0] : SSet.{u}) ≫ vertex x = vertex x :=
    (congrArg (fun f => f ≫ vertex x) (SSet.toDeltaZero_eq (𝟙 (Δ[0] : SSet.{u}))).symm).trans (Category.id_comp _)
  have hF : SSet.stdSimplex.δ (1 : Fin 2) ≫ t.val = vertex x :=
    (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ Δ[1] => f ≫ t.val) (SSet.frontInclusion_eq 0).symm).trans (t.2.1.trans hT)
  have hN : (coherentNerveFunctor.obj C).δ (1 : Fin 2) (enrichedEdge x y σ) = constantSimplex C ⦋0⦌ x :=
    (SSet.yonedaEquiv_naturality (SimplexCategory.δ (1 : Fin 2)) t.val).trans
      ((congrArg (fun f => SSet.yonedaEquiv f) hF).trans (SSet.yonedaEquiv.apply_symm_apply _))
  exact congrArg (fun s : CoherentSimplexIn C ⦋0⦌ => s.obj zeroPoint) hN

/-- The actual enriched edge ends at the supplied individual original target object. -/
theorem target (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋0⦌) :
    (enrichedEdge x y σ).obj (.mk (ULift.up (1 : Fin 2))) = y := by
  let t := (SSet.mappingSpaceRight.simplexEquivSucc _ _ _ 0) σ
  have hF : SSet.stdSimplex.δ (0 : Fin 2) ≫ t.val = vertex y :=
    (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ Δ[1] => f ≫ t.val) SSet.rightVertex_zero.symm).trans t.2.2
  have hN : (coherentNerveFunctor.obj C).δ (0 : Fin 2) (enrichedEdge x y σ) = constantSimplex C ⦋0⦌ y :=
    (SSet.yonedaEquiv_naturality (SimplexCategory.δ (0 : Fin 2)) t.val).trans
      ((congrArg (fun f => SSet.yonedaEquiv f) hF).trans (SSet.yonedaEquiv.apply_symm_apply _))
  exact congrArg (fun s : CoherentSimplexIn C ⦋0⦌ => s.obj zeroPoint) hN

/-- The whole original enriched edge retains both exact supplied object boundaries. -/
def fixedEdge (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋0⦌) :
    FixedSimplex x y (n := 0) := ⟨enrichedEdge x y σ, source x y σ, target x y σ⟩

/-- The supplied right-mapping-space vertex reads back its individual original enriched Hom vertex. -/
def read (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋0⦌) :
    (x ⟶[SSet.{u}] y) _⦋0⦌ := FixedEdgeReadback.readVertex x y (fixedEdge x y σ)

/-- The actual comparison reconstructs the entire supplied original right-mapping vertex. -/
theorem map_read (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋0⦌) :
    (HomMapping.map x y).app (op ⦋0⦌) (read x y σ) = σ := by
  apply (SSet.mappingSpaceRight.simplexEquivSucc _ _ _ 0).injective
  apply Subtype.ext
  have h := congrArg Subtype.val (FixedEdgeReadback.construct_read x y (fixedEdge x y σ))
  have hY := congrArg (fun s : coherentSimplex.{u} ⦋1⦌ ⟶ C =>
    (SSet.yonedaEquiv (X := coherentNerveFunctor.obj C) (n := ⦋1⦌)).symm s) h
  exact (HomMapping.map_readback x y (read x y σ)).trans
    (hY.trans (SSet.yonedaEquiv.symm_apply_apply _))

/-- The individual original enriched Hom vertex is retained by the actual mapping comparison and readback. -/
theorem read_map (τ : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    read x y ((HomMapping.map x y).app (op ⦋0⦌) τ) = τ :=
  HomMappingCells.map_injective x y (map_read x y _)

/-- The literal original Hom-vertex equivalence with right-mapping-space vertices, keeping the supplied
  individual objects. -/
def equiv : (x ⟶[SSet.{u}] y) _⦋0⦌ ≃
    (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) _⦋0⦌ where
  toFun := (HomMapping.map x y).app (op ⦋0⦌)
  invFun := read x y
  left_inv := read_map x y
  right_inv := map_read x y

end CategoryTheory.CoherentRealization.MappingVertices
