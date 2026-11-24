/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalZeroContraction
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0WeakEquivalence

import Mathlib.Tactic.FinCases

/-!
# Generic Stage-one degeneracy squares in the weak-stage diagonal

A morphism between degree-one weak stages gives a diagonal edge.  Its two
mixed degeneracies are diagonal `2`-simplices: one factors the edge through
the identity edge of its source and the other through the identity edge of
its target.  Their remaining sides are the Stage-zero map edges obtained by
reindexing the morphism.

The landed weak-equivalence triangles are specializations of these generic
constructions.  This file adds no Stage-one counit, arbitrary-edge
normalization, realization, K-zero, additivity, or Q/S claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- Underlying diagonal simplex induced by a generic Stage-one weak map. -/
noncomputable def stageWeakDiagonalStageOneMapSimplex
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (stageWeakDiagonal C).obj (op ⦋1⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₁ φ

/-- Source face of a generic Stage-one map simplex. -/
theorem stageWeakDiagonalStageOneMapSimplex_d1
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (stageWeakDiagonal C).δ 1
        (stageWeakDiagonalStageOneMapSimplex C φ) =
      ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 1)).obj A) := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalStageOneMapSimplex C φ) = _
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 1).op
          (stageWeakDiagonalStageOneMapSimplex C φ) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋0⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 1)).map
            (SimplexCategory.δ 1).op) (ComposableArrows.mk₁ φ)) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 1)).map
        (SimplexCategory.δ 1).op) (ComposableArrows.mk₁ φ) =
        ComposableArrows.mk₀ A := by
    apply ComposableArrows.ext₀
    rfl
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₀]

/-- Target face of a generic Stage-one map simplex. -/
theorem stageWeakDiagonalStageOneMapSimplex_d0
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalStageOneMapSimplex C φ) =
      ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 0)).obj B) := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalStageOneMapSimplex C φ) = _
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 0).op
          (stageWeakDiagonalStageOneMapSimplex C φ) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋0⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 1)).map
            (SimplexCategory.δ 0).op) (ComposableArrows.mk₁ φ)) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 1)).map
        (SimplexCategory.δ 0).op) (ComposableArrows.mk₁ φ) =
        ComposableArrows.mk₀ B := by
    apply ComposableArrows.ext₀
    rfl
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₀]

/-- Diagonal edge induced by a generic Stage-one weak map. -/
noncomputable def stageWeakDiagonalStageOneMapEdge
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (stageWeakDiagonal C).Edge
      (ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 1)).obj A))
      (ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 0)).obj B)) :=
  SSet.Edge.ofEq (SSet.Edge.mk'
    (stageWeakDiagonalStageOneMapSimplex C φ))
    (stageWeakDiagonalStageOneMapSimplex_d1 C φ)
    (stageWeakDiagonalStageOneMapSimplex_d0 C φ)

@[simp]
theorem stageWeakDiagonalStageOneMapEdge_edge
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (stageWeakDiagonalStageOneMapEdge C φ).edge =
      ComposableArrows.mk₁ φ :=
  rfl

/-- Identity edge of an arbitrary Stage-one weak object. -/
noncomputable abbrev stageWeakDiagonalStageOneIdentityEdge
    (A : StageWeakCategory C 1) :=
  stageWeakDiagonalStageOneMapEdge C (𝟙 A)

@[simp]
theorem stageWeakDiagonalStageOneIdentityEdge_edge
    (A : StageWeakCategory C 1) :
    (stageWeakDiagonalStageOneIdentityEdge C A).edge =
      ComposableArrows.mk₁ (𝟙 A) :=
  rfl

/-- Collapsed source-side degeneracy on objects:
`δ₀ ; σ₁ = σ₀ ; δ₀`. -/
theorem reindexStageWeak_sigmaOne_d0_obj
    (A : StageWeakCategory C 1) :
    (reindexStageWeak C (SimplexCategory.δ (0 : Fin 3))).obj
        ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).obj A) =
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
        ((reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).obj A) := by
  have hconst :
      SimplexCategory.δ (0 : Fin 3) ≫
          SimplexCategory.σ (1 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫
          SimplexCategory.δ (0 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    ext i
    fin_cases i <;> rfl
  change ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2)) ⋙
    reindexStageWeak C (SimplexCategory.δ (0 : Fin 3))).obj A) = _
  rw [← reindexStageWeak_comp, hconst, reindexStageWeak_comp]
  rfl

/-- Collapsed source-side degeneracy on maps, with explicit endpoint
transports. -/
theorem reindexStageWeak_sigmaOne_d0_map
    {A B : StageWeakCategory C 1} (φ : A ⟶ B)
    (hA := reindexStageWeak_sigmaOne_d0_obj C A)
    (hB := reindexStageWeak_sigmaOne_d0_obj C B) :
    (reindexStageWeak C (SimplexCategory.δ (0 : Fin 3))).map
        ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).map φ) =
      eqToHom hA ≫
        (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map
          ((reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).map φ) ≫
        eqToHom hB.symm := by
  have hconst :
      SimplexCategory.δ (0 : Fin 3) ≫
          SimplexCategory.σ (1 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫
          SimplexCategory.δ (0 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    ext i
    fin_cases i <;> rfl
  have hF : reindexStageWeak C (SimplexCategory.σ (1 : Fin 2)) ⋙
      reindexStageWeak C (SimplexCategory.δ (0 : Fin 3)) =
        reindexStageWeak C (SimplexCategory.δ (0 : Fin 2)) ⋙
          reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)) := by
    rw [← reindexStageWeak_comp, ← reindexStageWeak_comp, hconst]
  exact Functor.congr_hom hF φ

/-- Collapsed target-side degeneracy on objects:
`δ₂ ; σ₀ = σ₀ ; δ₁`. -/
theorem reindexStageWeak_sigmaZero_d2_obj
    (A : StageWeakCategory C 1) :
    (reindexStageWeak C (SimplexCategory.δ (2 : Fin 3))).obj
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).obj A) =
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
        ((reindexStageWeak C (SimplexCategory.δ (1 : Fin 2))).obj A) := by
  have hconst :
      SimplexCategory.δ (2 : Fin 3) ≫
          SimplexCategory.σ (0 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫
          SimplexCategory.δ (1 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    ext i
    fin_cases i <;> rfl
  change ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2)) ⋙
    reindexStageWeak C (SimplexCategory.δ (2 : Fin 3))).obj A) = _
  rw [← reindexStageWeak_comp, hconst, reindexStageWeak_comp]
  rfl

/-- Collapsed target-side degeneracy on maps, with explicit endpoint
transports. -/
theorem reindexStageWeak_sigmaZero_d2_map
    {A B : StageWeakCategory C 1} (φ : A ⟶ B)
    (hA := reindexStageWeak_sigmaZero_d2_obj C A)
    (hB := reindexStageWeak_sigmaZero_d2_obj C B) :
    (reindexStageWeak C (SimplexCategory.δ (2 : Fin 3))).map
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).map φ) =
      eqToHom hA ≫
        (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map
          ((reindexStageWeak C (SimplexCategory.δ (1 : Fin 2))).map φ) ≫
        eqToHom hB.symm := by
  have hconst :
      SimplexCategory.δ (2 : Fin 3) ≫
          SimplexCategory.σ (0 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫
          SimplexCategory.δ (1 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    ext i
    fin_cases i <;> rfl
  have hF : reindexStageWeak C (SimplexCategory.σ (0 : Fin 2)) ⋙
      reindexStageWeak C (SimplexCategory.δ (2 : Fin 3)) =
        reindexStageWeak C (SimplexCategory.δ (1 : Fin 2)) ⋙
          reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)) := by
    rw [← reindexStageWeak_comp, ← reindexStageWeak_comp, hconst]
  exact Functor.congr_hom hF φ

/-- Source mixed-degeneracy simplex for a generic Stage-one map. -/
noncomputable def stageWeakDiagonalStageOneSourceTriangleSimplex
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (stageWeakDiagonal C).obj (op ⦋2⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₂
    (𝟙 ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).obj A))
    ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).map φ)

@[simp]
theorem stageWeakDiagonalStageOneSourceTriangle_d2
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 2))
        (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) =
      (stageWeakDiagonalStageOneIdentityEdge C A).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) = _
  let A' := (reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).obj A
  let φ' := (reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).map φ
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 2).op
          (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 2))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 2).op)
            (ComposableArrows.mk₂ (𝟙 A') φ')) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 2).op)
        (ComposableArrows.mk₂ (𝟙 A') φ') =
      ComposableArrows.mk₁ (𝟙 A') :=
    CategoryTheory.nerve.δ₂_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁, Functor.map_id]
  have hδσ : SimplexCategory.δ (2 : Fin 3) ≫
      SimplexCategory.σ (1 : Fin 2) =
        𝟙 (⦋1⦌ : SimplexCategory) := by
    simpa using SimplexCategory.δ_comp_σ_succ
      (n := 1) (i := (1 : Fin 2))
  have hA := reindexStageWeak_sigma_delta_obj C A 1 2 hδσ
  exact ComposableArrows.ext₁ hA hA
    (reindexStageWeak_sigma_delta_map C (𝟙 A) 1 2 hδσ hA hA)

@[simp]
theorem stageWeakDiagonalStageOneSourceTriangle_d1
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 1))
        (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) =
      (stageWeakDiagonalStageOneMapEdge C φ).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) = _
  let A' := (reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).obj A
  let B' := (reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).obj B
  let φ' := (reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).map φ
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 1).op
          (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 1).op)
            (ComposableArrows.mk₂ (𝟙 A') φ')) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 1).op)
        (ComposableArrows.mk₂ (𝟙 A') φ') =
      ComposableArrows.mk₁ ((𝟙 A') ≫ φ') :=
    CategoryTheory.nerve.δ₁_mk₂_eq _ _
  rw [hstep, hface, Category.id_comp,
    CategoryTheory.nerveMap_app_mk₁]
  have hδσ : SimplexCategory.δ (1 : Fin 3) ≫
      SimplexCategory.σ (1 : Fin 2) =
        𝟙 (⦋1⦌ : SimplexCategory) := by
    simpa using SimplexCategory.δ_comp_σ_self
      (n := 1) (i := (1 : Fin 2))
  have hA := reindexStageWeak_sigma_delta_obj C A 1 1 hδσ
  have hB := reindexStageWeak_sigma_delta_obj C B 1 1 hδσ
  exact ComposableArrows.ext₁ hA hB
    (reindexStageWeak_sigma_delta_map C φ 1 1 hδσ hA hB)

@[simp]
theorem stageWeakDiagonalStageOneSourceTriangle_d0
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 0))
        (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) =
      (stageWeakDiagonalStageZeroMapEdge C
        ((reindexStageWeak C (SimplexCategory.δ 0)).map φ)).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) = _
  let A' := (reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).obj A
  let φ' := (reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).map φ
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 0).op
          (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 0).op)
            (ComposableArrows.mk₂ (𝟙 A') φ')) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 0).op)
        (ComposableArrows.mk₂ (𝟙 A') φ') =
      ComposableArrows.mk₁ φ' :=
    CategoryTheory.nerve.δ₀_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁]
  have hA := reindexStageWeak_sigmaOne_d0_obj C A
  have hB := reindexStageWeak_sigmaOne_d0_obj C B
  exact ComposableArrows.ext₁ hA hB
    (reindexStageWeak_sigmaOne_d0_map C φ hA hB)

/-- Source mixed-degeneracy triangle, oriented
`identityEdge A ; boundary₀ φ = mapEdge φ`. -/
noncomputable def stageWeakDiagonalStageOneSourceCompStruct
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    SSet.Edge.CompStruct
      (stageWeakDiagonalStageOneIdentityEdge C A)
      (stageWeakDiagonalStageZeroMapEdge C
        ((reindexStageWeak C (SimplexCategory.δ 0)).map φ))
      (stageWeakDiagonalStageOneMapEdge C φ) :=
  SSet.Edge.CompStruct.mk
    (stageWeakDiagonalStageOneSourceTriangleSimplex C φ)
    (stageWeakDiagonalStageOneSourceTriangle_d2 C φ)
    (stageWeakDiagonalStageOneSourceTriangle_d0 C φ)
    (stageWeakDiagonalStageOneSourceTriangle_d1 C φ)

/-- Target mixed-degeneracy simplex for a generic Stage-one map. -/
noncomputable def stageWeakDiagonalStageOneTargetTriangleSimplex
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (stageWeakDiagonal C).obj (op ⦋2⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₂
    ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).map φ)
    (𝟙 ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).obj B))

@[simp]
theorem stageWeakDiagonalStageOneTargetTriangle_d2
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 2))
        (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) =
      (stageWeakDiagonalStageZeroMapEdge C
        ((reindexStageWeak C (SimplexCategory.δ 1)).map φ)).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) = _
  let φ' := (reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).map φ
  let B' := (reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).obj B
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 2).op
          (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 2))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 2).op)
            (ComposableArrows.mk₂ φ' (𝟙 B'))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 2).op)
        (ComposableArrows.mk₂ φ' (𝟙 B')) =
      ComposableArrows.mk₁ φ' :=
    CategoryTheory.nerve.δ₂_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁]
  have hA := reindexStageWeak_sigmaZero_d2_obj C A
  have hB := reindexStageWeak_sigmaZero_d2_obj C B
  exact ComposableArrows.ext₁ hA hB
    (reindexStageWeak_sigmaZero_d2_map C φ hA hB)

@[simp]
theorem stageWeakDiagonalStageOneTargetTriangle_d0
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 0))
        (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) =
      (stageWeakDiagonalStageOneIdentityEdge C B).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) = _
  let B' := (reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).obj B
  let φ' := (reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).map φ
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 0).op
          (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 0).op)
            (ComposableArrows.mk₂ φ' (𝟙 B'))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 0).op)
        (ComposableArrows.mk₂ φ' (𝟙 B')) =
      ComposableArrows.mk₁ (𝟙 B') :=
    CategoryTheory.nerve.δ₀_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁, Functor.map_id]
  have hδσ : SimplexCategory.δ (0 : Fin 3) ≫
      SimplexCategory.σ (0 : Fin 2) =
        𝟙 (⦋1⦌ : SimplexCategory) := by
    simpa using SimplexCategory.δ_comp_σ_self
      (n := 1) (i := (0 : Fin 2))
  have hB := reindexStageWeak_sigma_delta_obj C B 0 0 hδσ
  exact ComposableArrows.ext₁ hB hB
    (reindexStageWeak_sigma_delta_map C (𝟙 B) 0 0 hδσ hB hB)

@[simp]
theorem stageWeakDiagonalStageOneTargetTriangle_d1
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 1))
        (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) =
      (stageWeakDiagonalStageOneMapEdge C φ).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) = _
  let A' := (reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).obj A
  let B' := (reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).obj B
  let φ' := (reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).map φ
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 1).op
          (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 1).op)
            (ComposableArrows.mk₂ φ' (𝟙 B'))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 1).op)
        (ComposableArrows.mk₂ φ' (𝟙 B')) =
      ComposableArrows.mk₁ (φ' ≫ 𝟙 B') :=
    CategoryTheory.nerve.δ₁_mk₂_eq _ _
  rw [hstep, hface, Category.comp_id,
    CategoryTheory.nerveMap_app_mk₁]
  have hδσ : SimplexCategory.δ (1 : Fin 3) ≫
      SimplexCategory.σ (0 : Fin 2) =
        𝟙 (⦋1⦌ : SimplexCategory) := by
    simpa using SimplexCategory.δ_comp_σ_succ
      (n := 1) (i := (0 : Fin 2))
  have hA := reindexStageWeak_sigma_delta_obj C A 0 1 hδσ
  have hB := reindexStageWeak_sigma_delta_obj C B 0 1 hδσ
  exact ComposableArrows.ext₁ hA hB
    (reindexStageWeak_sigma_delta_map C φ 0 1 hδσ hA hB)

/-- Target mixed-degeneracy triangle, oriented
`boundary₁ φ ; identityEdge B = mapEdge φ`. -/
noncomputable def stageWeakDiagonalStageOneTargetCompStruct
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    SSet.Edge.CompStruct
      (stageWeakDiagonalStageZeroMapEdge C
        ((reindexStageWeak C (SimplexCategory.δ 1)).map φ))
      (stageWeakDiagonalStageOneIdentityEdge C B)
      (stageWeakDiagonalStageOneMapEdge C φ) :=
  SSet.Edge.CompStruct.mk
    (stageWeakDiagonalStageOneTargetTriangleSimplex C φ)
    (stageWeakDiagonalStageOneTargetTriangle_d2 C φ)
    (stageWeakDiagonalStageOneTargetTriangle_d0 C φ)
    (stageWeakDiagonalStageOneTargetTriangle_d1 C φ)

/-- Fundamental-groupoid relation supplied by the source degeneracy square. -/
theorem stageWeakDiagonalStageOneSource_homMk_comp
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C A) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageZeroMapEdge C
          ((reindexStageWeak C (SimplexCategory.δ 0)).map φ)) =
    SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalStageOneMapEdge C φ) :=
  (stageWeakDiagonalStageOneSourceCompStruct C φ).homMk_comp

/-- Fundamental-groupoid relation supplied by the target degeneracy square. -/
theorem stageWeakDiagonalStageOneTarget_homMk_comp
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageZeroMapEdge C
          ((reindexStageWeak C (SimplexCategory.δ 1)).map φ)) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C B) =
    SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalStageOneMapEdge C φ) :=
  (stageWeakDiagonalStageOneTargetCompStruct C φ).homMk_comp

/-- The generic source triangle specializes to the landed weak-equivalence
triangle simplex. -/
theorem stageWeakDiagonalStageOneSourceTriangle_stageOneWeakMap
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    stageWeakDiagonalStageOneSourceTriangleSimplex C
        (stageOneWeakMap C f hf) =
      stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf :=
  rfl

/-- The generic target triangle specializes to the landed weak-equivalence
triangle simplex. -/
theorem stageWeakDiagonalStageOneTargetTriangle_stageOneWeakMap
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    stageWeakDiagonalStageOneTargetTriangleSimplex C
        (stageOneWeakMap C f hf) =
      stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf :=
  rfl

end CategoryTheory.Waldhausen.SConstruction

end
