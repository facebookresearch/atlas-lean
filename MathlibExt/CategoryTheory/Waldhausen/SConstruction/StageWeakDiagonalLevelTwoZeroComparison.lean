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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroCoherence

/-!
# G4 diagonal degree-two zero-comparison triangle

For exact categories `C`, `D`, `E` over the same universes with additive exact
`F : C ⥤ D` and `G : D ⥤ E`, construct a single degree-two weak stage over `E`
whose three diagonal faces are the `G`-mapped `F` zero edge, the `G` zero edge,
and the `(F ⋙ G)` zero edge. The underlying `Ar 2` diagram takes values
`G (F 0)` on left `0`, `G 0` on left `1`, and `0` on left `2`, with zero maps.
Its `δ₂`, `δ₀`, `δ₁` reindexings recover the mapped, `G`, and composite
level-zero edge diagrams, so `mk₂ 𝟙 𝟙` gives a diagonal `2`-simplex with those
three faces and a `SSet.Edge.CompStruct` triangle.

Triangle only. It provides no realization, paths, pointed maps, K-space
identity or composition laws, strict pointed functoriality, additivity, `π₀`,
spectra, or Q/S comparison.
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
variable (E : Type u) [Category.{v} E]
  [Preadditive E]
  [Limits.HasZeroObject E]
  [HasBinaryBiproducts E]
  [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]

/-- Object assignment: left `0` gives `G (F 0)`, left `1` gives `G 0`,
otherwise the chosen zero. All values are zero. -/
noncomputable def levelTwoZeroComparisonDiagramObj (A : Ar 2) : E :=
  if A.left = (0 : Fin 3) then G.obj (F.obj (0 : C))
  else if A.left = (1 : Fin 3) then G.obj (0 : D)
  else (0 : E)

omit [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C]
  [ExactCategory D] [F.IsExact] [HasBinaryBiproducts E] [ExactCategory E]
  [G.IsExact] in
/-- Every value of the comparison diagram is zero. -/
private theorem isZero_levelTwoZeroComparisonDiagramObj (A : Ar 2) :
    IsZero (levelTwoZeroComparisonDiagramObj C D F E G A) := by
  unfold levelTwoZeroComparisonDiagramObj
  by_cases h0 : A.left = (0 : Fin 3)
  · rw [ite_eq_left h0]
    exact G.map_isZero (F.map_isZero (isZero_zero C))
  · rw [ite_eq_right h0]
    by_cases h1 : A.left = (1 : Fin 3)
    · rw [ite_eq_left h1]
      exact G.map_isZero (isZero_zero D)
    · rw [ite_eq_right h1]
      exact isZero_zero E

/-- Canonical degree-two diagram with mapped, `G`, and composite faces
and zero maps. -/
noncomputable def levelTwoZeroComparisonDiagram : Ar 2 ⥤ E where
  obj := levelTwoZeroComparisonDiagramObj C D F E G
  map {A B} _ := 0
  map_id A := by
    have hZ := isZero_levelTwoZeroComparisonDiagramObj C D F E G A
    exact ((IsZero.iff_id_eq_zero _).mp hZ).symm
  map_comp {A B W} _ _ := by
    simp only [comp_zero]

omit [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C]
  [ExactCategory D] [F.IsExact] [G.IsExact] in
/-- The comparison diagram is a finite stage: all values zero,
all maps zero-isos. -/
theorem isStage_levelTwoZeroComparisonDiagram :
    (letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      IsStage 2 (levelTwoZeroComparisonDiagram C D F E G)) := by
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  exact isStage_of_pointwise_zero E _
    (isZero_levelTwoZeroComparisonDiagramObj C D F E G)

/-- Bundled degree-two stage for the comparison triangle. -/
noncomputable def levelTwoZeroComparisonStage :
    (letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      Stage E 2) := by
  letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  exact ⟨levelTwoZeroComparisonDiagram C D F E G, isStage_levelTwoZeroComparisonDiagram C D F E G⟩

/-- Weak degree-two stage for the comparison triangle. -/
noncomputable def levelTwoZeroComparisonWeak :
    (letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      StageWeakCategory E 2) := by
  letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  exact ⟨levelTwoZeroComparisonStage C D F E G⟩

omit [F.IsExact] in
/-- Reindexing along `δ 2` recovers the `G`-mapped `F` edge stage. -/
private theorem levelTwo_reindex_d2 :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (reindexStageWeak E (SimplexCategory.δ 2)).obj (levelTwoZeroComparisonWeak C D F E G) =
        (mapStageWeak D E G 1).obj (levelZeroEdgeWeak C D F)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  ext
  refine Functor.ext ?_ ?_
  · intro A
    by_cases hA0 : A.left = (0 : Fin 2)
    · have hmap : ((indexFunctor (SimplexCategory.δ 2)).obj A).left =
          (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 2)) A.left := rfl
      have hIdx : ((indexFunctor (SimplexCategory.δ 2)).obj A).left = (0 : Fin 3) := by
        rw [hmap, hA0]
        decide
      change (levelTwoZeroComparisonDiagramObj C D F E G
          ((indexFunctor (SimplexCategory.δ 2)).obj A)) =
        G.obj (levelZeroEdgeDiagramObj C D F A)
      simp only [levelTwoZeroComparisonDiagramObj, levelZeroEdgeDiagramObj, hIdx, hA0, ite_true]
    · have hA1 : A.left = (1 : Fin 2) := Fin.eq_one_of_ne_zero _ hA0
      have hmap : ((indexFunctor (SimplexCategory.δ 2)).obj A).left =
          (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 2)) A.left := rfl
      have hIdx : ((indexFunctor (SimplexCategory.δ 2)).obj A).left = (1 : Fin 3) := by
        rw [hmap, hA1]
        decide
      change (levelTwoZeroComparisonDiagramObj C D F E G
          ((indexFunctor (SimplexCategory.δ 2)).obj A)) =
        G.obj (levelZeroEdgeDiagramObj C D F A)
      simp only [levelTwoZeroComparisonDiagramObj, levelZeroEdgeDiagramObj, hIdx, hA1]
      simp
  · intro A B φ
    apply IsZero.eq_of_src
    change IsZero (levelTwoZeroComparisonDiagramObj C D F E G
      ((indexFunctor (SimplexCategory.δ 2)).obj A))
    exact isZero_levelTwoZeroComparisonDiagramObj C D F E G _

omit [F.IsExact] [G.IsExact] in
/-- Reindexing along `δ 0` recovers the `G` edge stage. -/
private theorem levelTwo_reindex_d0 :
    (letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (reindexStageWeak E (SimplexCategory.δ 0)).obj (levelTwoZeroComparisonWeak C D F E G) =
        levelZeroEdgeWeak D E G) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  ext
  refine Functor.ext ?_ ?_
  · intro A
    by_cases hA0 : A.left = (0 : Fin 2)
    · have hmap : ((indexFunctor (SimplexCategory.δ 0)).obj A).left =
          (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 0)) A.left := rfl
      have hIdx : ((indexFunctor (SimplexCategory.δ 0)).obj A).left = (1 : Fin 3) := by
        rw [hmap, hA0]
        decide
      change (levelTwoZeroComparisonDiagramObj C D F E G
          ((indexFunctor (SimplexCategory.δ 0)).obj A)) =
        levelZeroEdgeDiagramObj D E G A
      simp only [levelTwoZeroComparisonDiagramObj, levelZeroEdgeDiagramObj, hIdx, hA0, ite_true]
      simp
    · have hA1 : A.left = (1 : Fin 2) := Fin.eq_one_of_ne_zero _ hA0
      have hmap : ((indexFunctor (SimplexCategory.δ 0)).obj A).left =
          (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 0)) A.left := rfl
      have hIdx : ((indexFunctor (SimplexCategory.δ 0)).obj A).left = (2 : Fin 3) := by
        rw [hmap, hA1]
        decide
      change (levelTwoZeroComparisonDiagramObj C D F E G
          ((indexFunctor (SimplexCategory.δ 0)).obj A)) =
        levelZeroEdgeDiagramObj D E G A
      simp only [levelTwoZeroComparisonDiagramObj, levelZeroEdgeDiagramObj, hIdx, hA1]
      simp
  · intro A B φ
    apply IsZero.eq_of_src
    change IsZero (levelTwoZeroComparisonDiagramObj C D F E G
      ((indexFunctor (SimplexCategory.δ 0)).obj A))
    exact isZero_levelTwoZeroComparisonDiagramObj C D F E G _

omit [F.IsExact] [G.IsExact] in
/-- Reindexing along `δ 1` recovers the composite edge stage. -/
private theorem levelTwo_reindex_d1 :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (reindexStageWeak E (SimplexCategory.δ 1)).obj (levelTwoZeroComparisonWeak C D F E G) =
        levelZeroEdgeWeak C E (F ⋙ G)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  ext
  refine Functor.ext ?_ ?_
  · intro A
    by_cases hA0 : A.left = (0 : Fin 2)
    · have hmap : ((indexFunctor (SimplexCategory.δ 1)).obj A).left =
          (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 1)) A.left := rfl
      have hIdx : ((indexFunctor (SimplexCategory.δ 1)).obj A).left = (0 : Fin 3) := by
        rw [hmap, hA0]
        decide
      change (levelTwoZeroComparisonDiagramObj C D F E G
          ((indexFunctor (SimplexCategory.δ 1)).obj A)) =
        levelZeroEdgeDiagramObj C E (F ⋙ G) A
      simp only [levelTwoZeroComparisonDiagramObj, levelZeroEdgeDiagramObj, hIdx, hA0, ite_true]
      rfl
    · have hA1 : A.left = (1 : Fin 2) := Fin.eq_one_of_ne_zero _ hA0
      have hmap : ((indexFunctor (SimplexCategory.δ 1)).obj A).left =
          (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 1)) A.left := rfl
      have hIdx : ((indexFunctor (SimplexCategory.δ 1)).obj A).left = (2 : Fin 3) := by
        rw [hmap, hA1]
        decide
      change (levelTwoZeroComparisonDiagramObj C D F E G
          ((indexFunctor (SimplexCategory.δ 1)).obj A)) =
        levelZeroEdgeDiagramObj C E (F ⋙ G) A
      simp only [levelTwoZeroComparisonDiagramObj, levelZeroEdgeDiagramObj, hIdx, hA1]
      simp
  · intro A B φ
    apply IsZero.eq_of_src
    change IsZero (levelTwoZeroComparisonDiagramObj C D F E G
      ((indexFunctor (SimplexCategory.δ 1)).obj A))
    exact isZero_levelTwoZeroComparisonDiagramObj C D F E G _

/-- Underlying diagonal degree-two simplex from `mk₂ 𝟙 𝟙`. -/
noncomputable def levelTwoZeroComparisonSimplex :
    (letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonal E).obj (op ⦋2⦌)) := by
  letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₂ (𝟙 (levelTwoZeroComparisonWeak C D F E G))
    (𝟙 (levelTwoZeroComparisonWeak C D F E G))

/-- Second diagonal face is the `G`-mapped `F` zero edge. -/
theorem levelTwoZeroComparison_d2 :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonal E).δ 2 (levelTwoZeroComparisonSimplex C D F E G) =
        (stageWeakDiagonalMapLevelZeroEdge C D F E G).edge) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  change (stageWeakDiagonal E).map _ (levelTwoZeroComparisonSimplex C D F E G) = _
  have hstep : (stageWeakDiagonal E).map (SimplexCategory.δ 2).op
      (levelTwoZeroComparisonSimplex C D F E G) =
      (CategoryTheory.nerveMap (reindexStageWeak E (SimplexCategory.δ 2))).app (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory E 2)).map (SimplexCategory.δ 2).op)
          (ComposableArrows.mk₂ (𝟙 (levelTwoZeroComparisonWeak C D F E G))
            (𝟙 (levelTwoZeroComparisonWeak C D F E G)))) := rfl
  have hFace : (((CategoryTheory.nerve (StageWeakCategory E 2)).map
      (SimplexCategory.δ 2).op)
      (ComposableArrows.mk₂ (𝟙 (levelTwoZeroComparisonWeak C D F E G))
        (𝟙 (levelTwoZeroComparisonWeak C D F E G)))) =
      ComposableArrows.mk₁ (𝟙 (levelTwoZeroComparisonWeak C D F E G)) :=
    CategoryTheory.nerve.δ₂_mk₂_eq _ _
  rw [hstep, hFace, CategoryTheory.nerveMap_app_mk₁,
    stageWeakDiagonalMapLevelZeroEdge_edge]
  have hId1 : (reindexStageWeak E (SimplexCategory.δ 2)).map
      (𝟙 (levelTwoZeroComparisonWeak C D F E G)) =
      𝟙 ((reindexStageWeak E (SimplexCategory.δ 2)).obj
        (levelTwoZeroComparisonWeak C D F E G)) := by
    apply WideSubcategory.hom_ext
    simp
  have hId2 : (mapStageWeak D E G 1).map (𝟙 (levelZeroEdgeWeak C D F)) =
      𝟙 ((mapStageWeak D E G 1).obj (levelZeroEdgeWeak C D F)) := by
    simp
  rw [hId1, hId2, levelTwo_reindex_d2]

omit [F.IsExact] in
/-- Zeroth diagonal face is the `G` zero edge. -/
theorem levelTwoZeroComparison_d0 :
    (letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonal E).δ 0 (levelTwoZeroComparisonSimplex C D F E G) =
        (stageWeakDiagonalLevelZeroEdge D E G).edge) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  change (stageWeakDiagonal E).map _ (levelTwoZeroComparisonSimplex C D F E G) = _
  have hstep : (stageWeakDiagonal E).map (SimplexCategory.δ 0).op
      (levelTwoZeroComparisonSimplex C D F E G) =
      (CategoryTheory.nerveMap (reindexStageWeak E (SimplexCategory.δ 0))).app (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory E 2)).map (SimplexCategory.δ 0).op)
          (ComposableArrows.mk₂ (𝟙 (levelTwoZeroComparisonWeak C D F E G))
            (𝟙 (levelTwoZeroComparisonWeak C D F E G)))) := rfl
  have hFace : (((CategoryTheory.nerve (StageWeakCategory E 2)).map
      (SimplexCategory.δ 0).op)
      (ComposableArrows.mk₂ (𝟙 (levelTwoZeroComparisonWeak C D F E G))
        (𝟙 (levelTwoZeroComparisonWeak C D F E G)))) =
      ComposableArrows.mk₁ (𝟙 (levelTwoZeroComparisonWeak C D F E G)) :=
    CategoryTheory.nerve.δ₀_mk₂_eq _ _
  rw [hstep, hFace, CategoryTheory.nerveMap_app_mk₁,
    stageWeakDiagonalLevelZeroEdge_edge]
  have hId1 : (reindexStageWeak E (SimplexCategory.δ 0)).map
      (𝟙 (levelTwoZeroComparisonWeak C D F E G)) =
      𝟙 ((reindexStageWeak E (SimplexCategory.δ 0)).obj
        (levelTwoZeroComparisonWeak C D F E G)) := by
    apply WideSubcategory.hom_ext
    simp
  rw [hId1, levelTwo_reindex_d0]

/-- First diagonal face is the composite zero edge. -/
theorem levelTwoZeroComparison_d1 :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonal E).δ 1 (levelTwoZeroComparisonSimplex C D F E G) =
        (stageWeakDiagonalLevelZeroEdge C E (F ⋙ G)).edge) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E
  change (stageWeakDiagonal E).map _ (levelTwoZeroComparisonSimplex C D F E G) = _
  have hstep : (stageWeakDiagonal E).map (SimplexCategory.δ 1).op
      (levelTwoZeroComparisonSimplex C D F E G) =
      (CategoryTheory.nerveMap (reindexStageWeak E (SimplexCategory.δ 1))).app (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory E 2)).map (SimplexCategory.δ 1).op)
          (ComposableArrows.mk₂ (𝟙 (levelTwoZeroComparisonWeak C D F E G))
            (𝟙 (levelTwoZeroComparisonWeak C D F E G)))) := rfl
  have hcomp : (𝟙 (levelTwoZeroComparisonWeak C D F E G)) ≫
      (𝟙 (levelTwoZeroComparisonWeak C D F E G)) =
      𝟙 (levelTwoZeroComparisonWeak C D F E G) :=
    Category.id_comp _
  have hFace : (((CategoryTheory.nerve (StageWeakCategory E 2)).map
      (SimplexCategory.δ 1).op)
      (ComposableArrows.mk₂ (𝟙 (levelTwoZeroComparisonWeak C D F E G))
        (𝟙 (levelTwoZeroComparisonWeak C D F E G)))) =
      ComposableArrows.mk₁ ((𝟙 (levelTwoZeroComparisonWeak C D F E G)) ≫
        (𝟙 (levelTwoZeroComparisonWeak C D F E G))) :=
    CategoryTheory.nerve.δ₁_mk₂_eq _ _
  rw [hstep, hFace, hcomp, CategoryTheory.nerveMap_app_mk₁,
    stageWeakDiagonalLevelZeroEdge_edge]
  have hId1 : (reindexStageWeak E (SimplexCategory.δ 1)).map
      (𝟙 (levelTwoZeroComparisonWeak C D F E G)) =
      𝟙 ((reindexStageWeak E (SimplexCategory.δ 1)).obj
        (levelTwoZeroComparisonWeak C D F E G)) := by
    apply WideSubcategory.hom_ext
    simp
  rw [hId1, levelTwo_reindex_d1]

/-- Diagonal zero-comparison triangle with mapped, `G`, and composite faces. -/
noncomputable def levelTwoZeroComparisonCompStruct :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      SSet.Edge.CompStruct
        (stageWeakDiagonalMapLevelZeroEdge C D F E G)
        (stageWeakDiagonalLevelZeroEdge D E G)
        (stageWeakDiagonalLevelZeroEdge C E (F ⋙ G))) :=
  SSet.Edge.CompStruct.mk (levelTwoZeroComparisonSimplex C D F E G)
    (levelTwoZeroComparison_d2 C D F E G)
    (levelTwoZeroComparison_d0 C D F E G)
    (levelTwoZeroComparison_d1 C D F E G)

/-- Underlying `2`-simplex of the comparison triangle. -/
@[simp]
theorem levelTwoZeroComparisonCompStruct_simplex :
    (levelTwoZeroComparisonCompStruct C D F E G).simplex =
      levelTwoZeroComparisonSimplex C D F E G :=
  rfl

end CategoryTheory.Waldhausen.SConstruction
