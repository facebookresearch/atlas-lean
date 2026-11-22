/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.VertexRestriction
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# All-vertex restrictions of Reedy-fibrant simplicial spaces

For a Reedy-fibrant simplicial space, restriction from degree k to the product of degree-zero
spaces over all k + 1 vertices is a Kan fibration, and its fibre over any prescribed vertex
tuple is Kan. The same restriction commutes with target maps, reindexing by outer simplex
operators, and inner simplicial operators.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory

namespace SimplicialSpace.OriginalAllVertexReedy
open VertexRestriction

private theorem vertexRestriction_is_original_map (W : SimplicialSpace.{u}) (k : ℕ) :
    (discreteYonedaIso W k).inv ≫
      (discreteSourceMapping W).map (vertexInclusion k).op ≫
        (vertexMappingIso W k).hom =
      CategoryTheory.Limits.Pi.lift (fun i : Fin (k + 1) =>
        W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op) := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro i
  simp only [Category.assoc, CategoryTheory.Limits.Pi.lift_comp_π]
  rw [vertexMappingIso_leg]
  rw [← Functor.map_comp_assoc, ← op_comp, vertexInjection_inclusion]
  rw [discreteYonedaIso_naturality_index]
  simp only [Iso.inv_hom_id_assoc]

/-- Actual Reedy fibrancy gives the fibration of every literal original vertex restriction. -/
theorem allVertexMap_fibration (W : SimplicialSpace.{u}) (k : ℕ)
    (hW : IsFibrant W) :
    Fibration (CategoryTheory.Limits.Pi.lift (fun i : Fin (k + 1) =>
      W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op)) := by
  let : Mono (vertexInclusion.{u} k) := vertexInclusion_mono k
  let : Fibration ((discreteSourceMapping W).map (vertexInclusion k).op) :=
    discreteRestriction_fibration _ W hW
  rw [← vertexRestriction_is_original_map]
  infer_instance

/-- The original whole vertex square commutes with every space map at fixed arity. -/
theorem allVertexMap_target_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) (k : ℕ) :
    f.hom.app (op ⦋k⦌) ≫
        CategoryTheory.Limits.Pi.lift (fun i : Fin (k + 1) =>
            V.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op) =
      CategoryTheory.Limits.Pi.lift (fun i : Fin (k + 1) =>
          W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op) ≫
        CategoryTheory.Limits.Pi.map (fun _ : Fin (k + 1) => f.hom.app (op ⦋0⦌)) := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro i
  simp only [Category.assoc, CategoryTheory.Limits.Pi.lift_comp_π, CategoryTheory.Limits.Pi.map_π]
  rw [← Category.assoc, CategoryTheory.Limits.Pi.lift_comp_π]
  exact (f.hom.naturality (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op).symm

/-- All vertices reindex through any original simplex operator; no spine arity map is asserted. -/
theorem allVertexMap_index_naturality (W : SimplicialSpace.{u}) {m k : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋k⦌) :
    W.diagram.map θ.op ≫
        CategoryTheory.Limits.Pi.lift (fun i : Fin (m + 1) =>
            W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op) =
      CategoryTheory.Limits.Pi.lift (fun i : Fin (k + 1) =>
          W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op) ≫
        CategoryTheory.Limits.Pi.map' θ.toOrderHom (fun _ => 𝟙 (W.diagram _⦋0⦌)) := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro i
  simp only
      [Category.assoc, CategoryTheory.Limits.Pi.lift_comp_π, CategoryTheory.Limits.Pi.map'_comp_π,
        Category.comp_id]
  rw [← W.diagram.map_comp, ← op_comp, SimplexCategory.const_comp]

/-- Every inner operator acts through the same all-vertex arrow. -/
theorem allVertexMap_inner_naturality (W : SimplicialSpace.{u}) (k : ℕ)
    {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n) :
    (W.diagram _⦋k⦌).map θ ≫
      (CategoryTheory.Limits.Pi.lift (fun i : Fin (k + 1) =>
        W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op)).app n =
      (CategoryTheory.Limits.Pi.lift (fun i : Fin (k + 1) =>
        W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op)).app m ≫
        (∏ᶜ (fun _ : Fin (k + 1) => W.diagram _⦋0⦌)).map θ :=
  (CategoryTheory.Limits.Pi.lift (fun i : Fin (k + 1) =>
    W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op)).naturality θ

/-- The original fixed-tuple second projection is fibrant, with all vertices prescribed. -/
theorem fixedTupleProjection_fibration (W : SimplicialSpace.{u}) (k : ℕ)
    (hW : IsFibrant W) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    Fibration (pullback.snd
      (CategoryTheory.Limits.Pi.lift (fun i : Fin (k + 1) =>
          W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op))
      (CategoryTheory.Limits.Pi.lift (fun i => SSet.yonedaEquiv.symm (x i)))) := by
  let := allVertexMap_fibration W k hW
  infer_instance

/-- The literal fixed-tuple fibre is Kan over the same terminal Delta0 point. -/
theorem fixedTupleFibre_kanComplex (W : SimplicialSpace.{u}) (k : ℕ)
    (hW : IsFibrant W) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.KanComplex (pullback
      (CategoryTheory.Limits.Pi.lift (fun i : Fin (k + 1) =>
          W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op))
      (CategoryTheory.Limits.Pi.lift (fun i => SSet.yonedaEquiv.symm (x i)))) := by
  let := fixedTupleProjection_fibration W k hW x
  let pointIso : (Δ[0] : SSet.{u}) ≅ ⊤_ SSet.{u} :=
    SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso terminalIsTerminal
  have pointArrow : terminal.from (Δ[0] : SSet.{u}) = pointIso.hom :=
    Subsingleton.elim _ _
  let : IsFibrant (Δ[0] : SSet.{u}) := by
    change Fibration (terminal.from (Δ[0] : SSet.{u}))
    rw [pointArrow]
    infer_instance
  exact isFibrant_of_fibration (pullback.snd _ _)

end SimplicialSpace.OriginalAllVertexReedy
