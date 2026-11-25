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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonal
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalVertex
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZero
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFunctoriality

/-!
# Mapped-zero edge directly in the weak-stage diagonal

For exact categories `C` and `D` with an additive exact functor `F`,
construct a degree-one weak stage over `D` whose two diagonal faces are the
mapped chosen zero and the target chosen zero, and use its identity to define
an edge directly in `stageWeakDiagonal D` oriented mapped → target, with
source/target and underlying degree-one simplex computation laws.

This is a diagonal edge, distinct from the separate edge in the level-zero
`stageWeakNerve`; nerve `mk₀`/`mk₁` computation laws are reused rather than
restated.

Edge-only. It provides no realization, paths, pointed maps, additivity,
`π₀`/K₀, G-theory, spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial ZeroObject

open scoped Simplicial

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u₁) [Category.{v₁} C]
  [Preadditive C]
  [Limits.HasZeroObject C]
  [HasBinaryBiproducts C]
  [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D]
  [Preadditive D]
  [Limits.HasZeroObject D]
  [HasBinaryBiproducts D]
  [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- Object assignment: left endpoint `0` gives the mapped zero, otherwise the
chosen zero. `(0, 0)` and off-diagonal `(0, 1)` are mapped; `(1, 1)` is
chosen. All values are zero. -/
noncomputable def levelZeroEdgeDiagramObj (A : Ar 1) : D :=
  if A.left = (0 : Fin 2) then F.obj (0 : C) else (0 : D)

omit [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C]
  [ExactCategory D] [F.IsExact] in
/-- Every value of the edge diagram is zero. -/
private theorem isZero_levelZeroEdgeDiagramObj (A : Ar 1) :
    IsZero (levelZeroEdgeDiagramObj C D F A) := by
  unfold levelZeroEdgeDiagramObj
  by_cases h0 : A.left = (0 : Fin 2)
  · rw [ite_eq_left h0]
    exact F.map_isZero (isZero_zero C)
  · rw [ite_eq_right h0]
    exact isZero_zero D

/-- Canonical diagram with mapped/target diagonal faces and zero maps. -/
noncomputable def levelZeroEdgeDiagram : Ar 1 ⥤ D where
  obj := levelZeroEdgeDiagramObj C D F
  map {A B} _ := 0
  map_id A := by
    have hZ := isZero_levelZeroEdgeDiagramObj C D F A
    exact ((IsZero.iff_id_eq_zero _).mp hZ).symm
  map_comp {A B E} _ _ := by
    simp only [comp_zero]

omit [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C]
  [ExactCategory D] [F.IsExact] in
/-- Diagonal `(0, 0)` value is the mapped zero. -/
theorem levelZeroEdgeDiagram_diag_zero :
    (levelZeroEdgeDiagram C D F).obj (diag (0 : Fin 2)) = F.obj (0 : C) := by
  have hleft : (diag (0 : Fin 2) : Ar 1).left = (0 : Fin 2) := rfl
  simp [levelZeroEdgeDiagram, levelZeroEdgeDiagramObj, hleft]

omit [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C]
  [ExactCategory D] [F.IsExact] in
/-- Diagonal `(1, 1)` value is the chosen zero. -/
theorem levelZeroEdgeDiagram_diag_one :
    (levelZeroEdgeDiagram C D F).obj (diag (1 : Fin 2)) = (0 : D) := by
  have hleft : (diag (1 : Fin 2) : Ar 1).left = (1 : Fin 2) := rfl
  simp [levelZeroEdgeDiagram, levelZeroEdgeDiagramObj, hleft]

omit [HasBinaryBiproducts C] [ExactCategory C] [F.IsExact] in
/-- The edge diagram is a finite stage: all values zero, all maps zero-isos. -/
theorem isStage_levelZeroEdgeDiagram :
    (letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      IsStage 1 (levelZeroEdgeDiagram C D F)) := by
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact isStage_of_pointwise_zero D _ (isZero_levelZeroEdgeDiagramObj C D F)

/-- Bundled degree-one stage with mapped/target diagonal faces. -/
noncomputable def levelZeroEdgeStage :
    (letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      Stage D 1) := by
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact ⟨levelZeroEdgeDiagram C D F, isStage_levelZeroEdgeDiagram C D F⟩

/-- Weak degree-one stage with mapped/target diagonal faces. -/
noncomputable def levelZeroEdgeWeak :
    (letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      StageWeakCategory D 1) := by
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact ⟨levelZeroEdgeStage C D F⟩

/-- Mapped-zero vertex in the diagonal, as `mk₀` of the mapped zero stage. -/
noncomputable def levelZeroEdgeMappedVertex :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonal D).obj (op ⦋0⦌)) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact ComposableArrows.mk₀ ((mapStageWeak C D F 0).obj ⟨stageZero C⟩)

/-- Underlying degree-one diagonal simplex from the identity on the edge stage. -/
noncomputable def levelZeroEdgeSimplex :
    (letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonal D).obj (op ⦋1⦌)) := by
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact ComposableArrows.mk₁ (𝟙 (levelZeroEdgeWeak C D F))

/-- Reindexing along `δ 1` recovers the mapped zero stage. -/
theorem levelZeroEdge_reindex_src :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (reindexStageWeak D (SimplexCategory.δ 1)).obj (levelZeroEdgeWeak C D F) =
        (mapStageWeak C D F 0).obj ⟨stageZero C⟩) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  ext
  refine Functor.ext ?_ ?_
  · intro A
    have hlen : ⦋0⦌.len = 0 := rfl
    have : Subsingleton (Fin (⦋0⦌.len + 1)) := by
      rw [hlen]
      change Subsingleton (Fin 1)
      infer_instance
    have hA : A.left = (0 : Fin (⦋0⦌.len + 1)) := Subsingleton.elim _ _
    have hIdx : ((indexFunctor (SimplexCategory.δ 1)).obj A).left = (0 : Fin 2) := by
      have hmap : ((indexFunctor (SimplexCategory.δ 1)).obj A).left =
          (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 1)) A.left := rfl
      rw [hmap, hA]
      decide
    change (levelZeroEdgeDiagramObj C D F ((indexFunctor (SimplexCategory.δ 1)).obj A)) =
      F.obj (0 : C)
    simp only [levelZeroEdgeDiagramObj, hIdx, ite_true]
  · intro A B φ
    apply IsZero.eq_of_src
    change IsZero (levelZeroEdgeDiagramObj C D F ((indexFunctor (SimplexCategory.δ 1)).obj A))
    exact isZero_levelZeroEdgeDiagramObj C D F _

omit [HasBinaryBiproducts C] [ExactCategory C] [F.IsExact] in
/-- Reindexing along `δ 0` recovers the target zero stage. -/
theorem levelZeroEdge_reindex_tgt :
    (letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (reindexStageWeak D (SimplexCategory.δ 0)).obj (levelZeroEdgeWeak C D F) =
        (⟨stageZero D⟩ : StageWeakCategory D 0)) := by
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  ext
  refine Functor.ext ?_ ?_
  · intro A
    have hlen : ⦋0⦌.len = 0 := rfl
    have : Subsingleton (Fin (⦋0⦌.len + 1)) := by
      rw [hlen]
      change Subsingleton (Fin 1)
      infer_instance
    have hA : A.left = (0 : Fin (⦋0⦌.len + 1)) := Subsingleton.elim _ _
    have hIdx : ¬ (((indexFunctor (SimplexCategory.δ 0)).obj A).left = (0 : Fin 2)) := by
      have hmap : ((indexFunctor (SimplexCategory.δ 0)).obj A).left =
          (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ 0)) A.left := rfl
      rw [hmap, hA]
      decide
    change (levelZeroEdgeDiagramObj C D F ((indexFunctor (SimplexCategory.δ 0)).obj A)) =
      (0 : D)
    simp only [levelZeroEdgeDiagramObj, hIdx, ite_false]
  · intro A B φ
    apply (isZero_zero D).eq_of_src

omit [HasBinaryBiproducts C] [ExactCategory C] [F.IsExact] in
/-- Inner nerve face of the identity is the vertex. -/
private theorem levelZeroEdge_inner_face (i : Fin 2) :
    (letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      ((CategoryTheory.nerve (StageWeakCategory D 1)).map
        (SimplexCategory.δ i).op) (ComposableArrows.mk₁ (𝟙 (levelZeroEdgeWeak C D F))) =
        ComposableArrows.mk₀ (levelZeroEdgeWeak C D F)) := by
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  apply ComposableArrows.ext₀
  fin_cases i <;> rfl

omit [F.IsExact] in
/-- Diagonal source face is `mk₀` of the `δ 1` reindexing. -/
theorem levelZeroEdge_diag_src :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonal D).δ 1 (levelZeroEdgeSimplex C D F) =
        ComposableArrows.mk₀
          ((reindexStageWeak D (SimplexCategory.δ 1)).obj (levelZeroEdgeWeak C D F))) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  change (stageWeakDiagonal D).map _ (levelZeroEdgeSimplex C D F) = _
  have hstep : (stageWeakDiagonal D).map (SimplexCategory.δ 1).op
      (levelZeroEdgeSimplex C D F) =
      (CategoryTheory.nerveMap (reindexStageWeak D (SimplexCategory.δ 1))).app (op ⦋0⦌)
        (((CategoryTheory.nerve (StageWeakCategory D 1)).map (SimplexCategory.δ 1).op)
          (ComposableArrows.mk₁ (𝟙 (levelZeroEdgeWeak C D F)))) := rfl
  rw [hstep, levelZeroEdge_inner_face, CategoryTheory.nerveMap_app_mk₀]

omit [HasBinaryBiproducts C] [ExactCategory C] [F.IsExact] in
/-- Diagonal target face is `mk₀` of the `δ 0` reindexing. -/
theorem levelZeroEdge_diag_tgt :
    (letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonal D).δ 0 (levelZeroEdgeSimplex C D F) =
        ComposableArrows.mk₀
          ((reindexStageWeak D (SimplexCategory.δ 0)).obj (levelZeroEdgeWeak C D F))) := by
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  change (stageWeakDiagonal D).map _ (levelZeroEdgeSimplex C D F) = _
  have hstep : (stageWeakDiagonal D).map (SimplexCategory.δ 0).op
      (levelZeroEdgeSimplex C D F) =
      (CategoryTheory.nerveMap (reindexStageWeak D (SimplexCategory.δ 0))).app (op ⦋0⦌)
        (((CategoryTheory.nerve (StageWeakCategory D 1)).map (SimplexCategory.δ 0).op)
          (ComposableArrows.mk₁ (𝟙 (levelZeroEdgeWeak C D F)))) := rfl
  rw [hstep, levelZeroEdge_inner_face, CategoryTheory.nerveMap_app_mk₀]

/-- The mapped-zero edge directly in the weak-stage diagonal, mapped → target. -/
noncomputable def stageWeakDiagonalLevelZeroEdge :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonal D).Edge
        (levelZeroEdgeMappedVertex C D F) (stageWeakDiagonalZeroVertex D)) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  refine SSet.Edge.ofEq (SSet.Edge.mk' (levelZeroEdgeSimplex C D F)) ?_ ?_
  · rw [levelZeroEdge_diag_src, levelZeroEdge_reindex_src]
    rfl
  · rw [levelZeroEdge_diag_tgt, levelZeroEdge_reindex_tgt]
    rfl

/-- Underlying simplex computation: the edge uses `mk₁` of the identity. -/
@[simp]
theorem stageWeakDiagonalLevelZeroEdge_edge :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalLevelZeroEdge C D F).edge =
        ComposableArrows.mk₁ (𝟙 (levelZeroEdgeWeak C D F))) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  rfl

/-- Source of the level-zero edge is the mapped-zero vertex. -/
@[simp]
theorem stageWeakDiagonalLevelZeroEdge_src :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonal D).δ 1 (stageWeakDiagonalLevelZeroEdge C D F).edge =
        levelZeroEdgeMappedVertex C D F) :=
  SSet.Edge.src_eq _

/-- Target of the level-zero edge is the target-zero vertex. -/
@[simp]
theorem stageWeakDiagonalLevelZeroEdge_tgt :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonal D).δ 0 (stageWeakDiagonalLevelZeroEdge C D F).edge =
        stageWeakDiagonalZeroVertex D) :=
  SSet.Edge.tgt_eq _

end CategoryTheory.Waldhausen.SConstruction
