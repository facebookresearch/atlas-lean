/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Chosen spine-vertex fibration via the original vertex-coproduct construction.
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalEveryVertexComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.VertexRestriction
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Fibrations from spine tuples to vertex products

For a Reedy fibrant simplicial space and spine arity at least two, the chosen-spine tuple map to
the ordered vertex product is a fibration. The map is identified, through the spine and vertex
mapping isomorphisms, with restriction along the vertex-coproduct inclusion into the spine.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory

namespace SimplicialSpace.OriginalChosenSpineFibration
open FixedTupleSpinePrefix OriginalChosenSpineFixedTupleBaseChange
open VertexRestriction


/-- Every original spine vertex factors through its actual adjacent edge, with the first endpoint
retained. -/
private def spineVertexPoint (k : ℕ) (hk : 2 ≤ k) (i : Fin (k + 1)) :
    (Δ[0] : SSet.{u}) ⟶ (SSet.Rezk.spineSubcomplex.{u} k : SSet.{u}) :=
  Fin.cases
    (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
      SSet.Rezk.spineEdgeInclusion k (⟨0, by omega⟩ : Fin k))
    (fun j => SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
      SSet.Rezk.spineEdgeInclusion k j) i

private theorem spineVertexPoint_include (k : ℕ) (hk : 2 ≤ k) (i : Fin (k + 1)) :
    spineVertexPoint k hk i ≫ (SSet.Rezk.spineSubcomplex.{u} k).ι =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [spineVertexPoint, Fin.cases_zero, Category.assoc,
      SSet.Rezk.spineEdgeInclusion_ι]
    rw [← SSet.stdSimplex.map_comp]
    congr 1
    ext a
    fin_cases a
    rfl
  · simp only [spineVertexPoint, Fin.cases_succ, Category.assoc,
      SSet.Rezk.spineEdgeInclusion_ι]
    rw [← SSet.stdSimplex.map_comp]
    congr 1
    ext a
    fin_cases a
    rfl

/-- The whole vertex object enters the actual full spine by its proven coproduct universal
property. -/
private def spineVertexEmbedding (k : ℕ) (hk : 2 ≤ k) :
    vertexObject.{u} k ⟶ (SSet.Rezk.spineSubcomplex.{u} k : SSet.{u}) :=
  (vertexCofanIsColimit k).desc (Cofan.mk _ (spineVertexPoint k hk))

private theorem spineVertexEmbedding_injection (k : ℕ) (hk : 2 ≤ k) (i : Fin (k + 1)) :
    vertexInjection k i ≫ spineVertexEmbedding k hk = spineVertexPoint k hk i :=
  (vertexCofanIsColimit k).fac (Cofan.mk _ (spineVertexPoint k hk)) ⟨i⟩

/-- Its inclusion in the simplex is the SAME original injective all-vertex map. -/
private theorem spineVertexEmbedding_include (k : ℕ) (hk : 2 ≤ k) :
    spineVertexEmbedding k hk ≫ (SSet.Rezk.spineSubcomplex.{u} k).ι = vertexInclusion k := by
  apply (vertexCofanIsColimit k).hom_ext
  rintro ⟨i⟩
  change vertexInjection k i ≫ (spineVertexEmbedding k hk ≫
    (SSet.Rezk.spineSubcomplex.{u} k).ι) = vertexInjection k i ≫ vertexInclusion k
  rw [← Category.assoc, spineVertexEmbedding_injection, spineVertexPoint_include,
    vertexInjection_inclusion]

private theorem spineVertexEmbedding_mono (k : ℕ) (hk : 2 ≤ k) :
    Mono (spineVertexEmbedding.{u} k hk) := by
  let : Mono (vertexInclusion.{u} k) := vertexInclusion_mono k
  exact mono_of_mono_fac (spineVertexEmbedding_include k hk)

/-- The actual vertex restriction of the original spine mapping object is the chosen-spine tuple
arrow. -/
private theorem spineVertexRestriction_is_chosenMap (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k) :
    (segalSpineMappingIso W k hk).inv ≫
        (discreteSourceMapping W).map (spineVertexEmbedding k hk).op ≫
          (vertexMappingIso W k).hom = chosenSpineVertexMap W k hk := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro i
  simp only [Category.assoc]
  rw [vertexMappingIso_leg]
  rw [← Functor.map_comp_assoc, ← op_comp, spineVertexEmbedding_injection]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [spineVertexPoint, Fin.cases_zero, op_comp, Functor.map_comp, Category.assoc]
    rw [discreteYonedaIso_naturality_index W (SimplexCategory.δ (1 : Fin 2))]
    simpa only [chosenSpineVertexMap, tupleVertexMap, Category.assoc,
      CategoryTheory.Limits.Pi.lift_comp_π, vertexProjection, Fin.cases_zero,
      segalStrictEdgeProjection, SimplicialObject.δ_def] using
      (congrArg (fun q => q ≫ W.diagram.δ (1 : Fin 2))
        (fullPrefixChosenIso_edge W k hk (⟨0, by omega⟩ : Fin k))).symm
  · simp only [spineVertexPoint, Fin.cases_succ, op_comp, Functor.map_comp, Category.assoc]
    rw [discreteYonedaIso_naturality_index W (SimplexCategory.δ (0 : Fin 2))]
    simpa only [chosenSpineVertexMap, tupleVertexMap, Category.assoc,
      CategoryTheory.Limits.Pi.lift_comp_π, vertexProjection, Fin.cases_succ,
      segalStrictEdgeProjection, SimplicialObject.δ_def] using
      (congrArg (fun q => q ≫ W.diagram.δ (0 : Fin 2))
        (fullPrefixChosenIso_edge W k hk j)).symm

/-- Reedy fibrancy alone makes the actual full-spine tuple projection a fibration.
The statement uses the original chosen arrow and the vertex-coproduct construction above. -/
theorem chosenSpineVertexMap_fibration (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k) (hW : IsFibrant W) :
    Fibration (chosenSpineVertexMap W k hk) := by
  let : Mono (spineVertexEmbedding.{u} k hk) := spineVertexEmbedding_mono k hk
  let : Fibration ((discreteSourceMapping W).map (spineVertexEmbedding k hk).op) :=
    discreteRestriction_fibration _ W hW
  rw [← spineVertexRestriction_is_chosenMap]
  infer_instance

end SimplicialSpace.OriginalChosenSpineFibration
