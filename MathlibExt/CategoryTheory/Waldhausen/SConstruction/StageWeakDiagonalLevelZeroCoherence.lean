/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroEdge
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalMap

/-!
# Diagonal level-zero composition coherence

For exact categories over the same universes with their local standard
Waldhausen structures, transport the diagonal mapped-zero edge
`stageWeakDiagonalLevelZeroEdge` through a second exact-functor diagonal map.
The transported edge runs from the composite mapped-zero vertex to the
once-mapped zero vertex, with edge-formula and endpoint laws in the same
`mk₁`/`ofEq` representation as the levelwise mapped comparison edge.
Endpoint alignment reuses `stageWeakDiagonalMap_app_mk₀`,
`stageWeakDiagonalMap_zeroVertex`, and `mapStageWeak_comp`; the vertex
identity case reuses `mapStageWeak_id`. The levelwise identity and composition
laws in `StageWeakDiagonalZeroComparisonCoherence` are the direct analogues
justifying this shape. Degenerate composition coherence is the library
`CompStruct.idComp`/`compId` at the diagonal level-zero edge, so no new
homotopy framework is introduced.

Edge-only in the weak-stage diagonal. It provides no realization, paths,
pointed maps, additivity, `π₀`/K₀, G-theory, spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial ZeroObject

open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- Mapped-vertex identity over the identity functor. -/
theorem stageWeakDiagonalLevelZero_mappedVertex_id :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      levelZeroEdgeMappedVertex C C (𝟭 C) = stageWeakDiagonalZeroVertex C) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  unfold levelZeroEdgeMappedVertex stageWeakDiagonalZeroVertex
  rw [mapStageWeak_id]
  rfl

/-- Mapped diagonal level-zero edge: the `F` edge transported through the `G`
diagonal map, with source aligned to the `F ⋙ G` mapped zero vertex. -/
noncomputable def stageWeakDiagonalMapLevelZeroEdge (E : Type u)
    [Category.{v} E] [Preadditive E] [Limits.HasZeroObject E]
    [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonal E).Edge
        (levelZeroEdgeMappedVertex C E (F ⋙ G))
        (levelZeroEdgeMappedVertex D E G)) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  refine SSet.Edge.ofEq
    ((stageWeakDiagonalLevelZeroEdge C D F).map
      (stageWeakDiagonalMap D E G)) ?_ ?_
  · unfold levelZeroEdgeMappedVertex
    rw [stageWeakDiagonalMap_app_mk₀, mapStageWeak_comp]
    rfl
  · unfold levelZeroEdgeMappedVertex
    rw [stageWeakDiagonalMap_zeroVertex]
    rfl

/-- Edge formula for the mapped diagonal level-zero edge. -/
theorem stageWeakDiagonalMapLevelZeroEdge_edge (E : Type u)
    [Category.{v} E] [Preadditive E] [Limits.HasZeroObject E]
    [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonalMapLevelZeroEdge C D F E G).edge =
        ComposableArrows.mk₁ ((mapStageWeak D E G 1).map
          (𝟙 (levelZeroEdgeWeak C D F)))) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  have h1 : (stageWeakDiagonalMapLevelZeroEdge C D F E G).edge =
      ((stageWeakDiagonalMap D E G).app (op ⦋1⦌))
        (stageWeakDiagonalLevelZeroEdge C D F).edge := rfl
  rw [h1, stageWeakDiagonalLevelZeroEdge_edge, stageWeakDiagonalMap_app]
  exact stageWeakNerveMap_app_mk₁ D E G _ _

/-- Source face of the mapped diagonal level-zero edge. -/
@[simp]
theorem stageWeakDiagonalMapLevelZeroEdge_src (E : Type u)
    [Category.{v} E] [Preadditive E] [Limits.HasZeroObject E]
    [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (ConcreteCategory.hom
        (X := (CategoryTheory.nerve (StageWeakCategory E (0 + 1))).obj (op ⦋0 + 1⦌))
        (Y := (CategoryTheory.nerve (StageWeakCategory E 0)).obj (op ⦋0⦌))
        ((stageWeakDiagonal E).δ 1))
        (stageWeakDiagonalMapLevelZeroEdge C D F E G).edge =
      levelZeroEdgeMappedVertex C E (F ⋙ G)) :=
  SSet.Edge.src_eq _

/-- Target face of the mapped diagonal level-zero edge. -/
@[simp]
theorem stageWeakDiagonalMapLevelZeroEdge_tgt (E : Type u)
    [Category.{v} E] [Preadditive E] [Limits.HasZeroObject E]
    [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (ConcreteCategory.hom
        (X := (CategoryTheory.nerve (StageWeakCategory E (0 + 1))).obj (op ⦋0 + 1⦌))
        (Y := (CategoryTheory.nerve (StageWeakCategory E 0)).obj (op ⦋0⦌))
        ((stageWeakDiagonal E).δ 0))
        (stageWeakDiagonalMapLevelZeroEdge C D F E G).edge =
      levelZeroEdgeMappedVertex D E G) :=
  SSet.Edge.tgt_eq _

/-- Reindexing the degree-zero stage along `σ 0` is the identity edge stage.
Narrow helper for the identity edge below. -/
private theorem levelZeroEdgeWeak_id_reindex :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj ⟨stageZero C⟩ =
        levelZeroEdgeWeak C C (𝟭 C)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  ext
  refine Functor.ext ?_ ?_
  · intro A
    have hR : levelZeroEdgeDiagramObj C C (𝟭 C) A = (0 : C) := by
      unfold levelZeroEdgeDiagramObj
      by_cases h0 : A.left = (0 : Fin 2)
      · simp only [h0, ite_true, Functor.id_obj]
      · simp only [h0, ite_false]
    change (zeroDiagram C 0).obj
        ((indexFunctor (SimplexCategory.σ (0 : Fin 1))).obj A) =
      levelZeroEdgeDiagramObj C C (𝟭 C) A
    rw [hR]
    rfl
  · intro A B φ
    apply IsZero.eq_of_src
    change IsZero ((zeroDiagram C 0).obj
      ((indexFunctor (SimplexCategory.σ (0 : Fin 1))).obj A))
    exact isZero_zero C

/-- Identity degeneracy for the diagonal level-zero edge (mapped → target;
`δ 1` source, `δ 0` target): transporting `SSet.Edge.id
(stageWeakDiagonalZeroVertex C)` along
`stageWeakDiagonalLevelZero_mappedVertex_id` gives
`stageWeakDiagonalLevelZeroEdge C C (𝟭 C)`. Edge-only; no strict functoriality,
composition, additivity, or `π₀` claim. -/
theorem stageWeakDiagonalLevelZeroEdge_id :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      SSet.Edge.ofEq
        (SSet.Edge.id (stageWeakDiagonalZeroVertex C))
        (stageWeakDiagonalLevelZero_mappedVertex_id C).symm rfl =
      stageWeakDiagonalLevelZeroEdge C C (𝟭 C)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  have hσ : (stageWeakDiagonal C).σ (0 : Fin 1)
      (stageWeakDiagonalZeroVertex C) =
      ComposableArrows.mk₁ (𝟙 ((reindexStageWeak C
        (SimplexCategory.σ (0 : Fin 1))).obj ⟨stageZero C⟩)) := by
    change (stageWeakDiagonal C).map (SimplexCategory.σ (0 : Fin 1)).op
      (stageWeakDiagonalZeroVertex C) = _
    rw [stageWeakDiagonal_map]
    change (CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)))).app (op ⦋0 + 1⦌)
        ((CategoryTheory.nerve (StageWeakCategory C 0)).map
          (SimplexCategory.σ (0 : Fin 1)).op (stageWeakDiagonalZeroVertex C)) = _
    have hInner : (CategoryTheory.nerve (StageWeakCategory C 0)).map
        (SimplexCategory.σ (0 : Fin 1)).op
        (stageWeakDiagonalZeroVertex C) =
        ComposableArrows.mk₁ (𝟙 (⟨stageZero C⟩ : StageWeakCategory C 0)) :=
      CategoryTheory.nerve.σ₀_mk₀_eq _
    rw [hInner, CategoryTheory.nerveMap_app_mk₁, Functor.map_id]
  apply SSet.Edge.ext
  change (stageWeakDiagonal C).σ (0 : Fin 1)
      (stageWeakDiagonalZeroVertex C) =
    (stageWeakDiagonalLevelZeroEdge C C (𝟭 C)).edge
  rw [hσ, levelZeroEdgeWeak_id_reindex, stageWeakDiagonalLevelZeroEdge_edge]

end CategoryTheory.Waldhausen.SConstruction
