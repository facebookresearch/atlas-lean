/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Simplices
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

import Mathlib.Tactic.FinCases

/-!
# Weak-equivalence relations between diagonal K-zero object edges

A weak equivalence `f : X ⟶ Y` induces a pointwise weak morphism between the
canonical degree-one stages.  Two mixed degeneracy `2`-simplices compare the
resulting diagonal weak edge with the object edges of `X` and `Y`; their
remaining faces are the degenerate edge at the diagonal zero vertex.  The
two composition relations therefore identify the object edges in the
simplicial fundamental groupoid.

This file uses neither a cofibration hypothesis nor gluing, saturation, or
two-out-of-three.  It makes no K-zero comparison, generation, realization,
additivity, model-category, or higher K-theory claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- A weak equivalence induces the corresponding morphism between canonical
degree-one weak stages. -/
noncomputable def stageOneWeakMap {X Y : C} (f : X ⟶ Y)
    (hf : IsWeakEquivalence f) :
    stageOneWeakObj C X ⟶ stageOneWeakObj C Y := by
  refine ⟨(stageOne C).map f, ?_⟩
  change ∀ A, IsWeakEquivalence (((stageOne C).map f).hom.app A)
  intro A
  by_cases hA : A.left = A.right
  · have hX : IsZero (((stageOne C).obj X).obj.obj A) := by
      change IsZero (stageOneDiagramObj C X A)
      rw [stageOneDiagramObj_of_eq C X hA]
      exact isZero_zero C
    have hY : IsZero (((stageOne C).obj Y).obj.obj A) := by
      change IsZero (stageOneDiagramObj C Y A)
      rw [stageOneDiagramObj_of_eq C Y hA]
      exact isZero_zero C
    let _ : IsIso (((stageOne C).map f).hom.app A) :=
      hX.isIso hY _
    exact (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).of_isIso _
  · have hA01 : A = interval (0 : Fin 2) 1 (by decide) :=
      ar1_eq_interval01_of_ne hA
    subst A
    rw [stageOne_map_interval_zero_one]
    exact hf

@[simp]
theorem stageOneWeakMap_hom {X Y : C} (f : X ⟶ Y)
    (hf : IsWeakEquivalence f) :
    (stageOneWeakMap C f hf).hom = (stageOne C).map f :=
  rfl

/-- Underlying diagonal edge simplex induced by a weak equivalence. -/
noncomputable def stageWeakDiagonalWeakEquivalenceSimplex
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (stageWeakDiagonal C).obj (op ⦋1⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₁ (stageOneWeakMap C f hf)

/-- The source face of the weak-equivalence simplex is the diagonal zero
vertex. -/
theorem stageWeakDiagonalWeakEquivalenceSimplex_d1
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (stageWeakDiagonal C).δ 1
        (stageWeakDiagonalWeakEquivalenceSimplex C f hf) =
      stageWeakDiagonalZeroVertex C := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalWeakEquivalenceSimplex C f hf) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 1).op
      (stageWeakDiagonalWeakEquivalenceSimplex C f hf) =
      (CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋0⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 1)).map
          (SimplexCategory.δ 1).op)
          (ComposableArrows.mk₁ (stageOneWeakMap C f hf))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 1)).map
        (SimplexCategory.δ 1).op)
        (ComposableArrows.mk₁ (stageOneWeakMap C f hf)) =
      ComposableArrows.mk₀ (stageOneWeakObj C X) := by
    apply ComposableArrows.ext₀
    rfl
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₀]
  change ComposableArrows.mk₀
      (⟨(reindexStage (C := C) (SimplexCategory.δ 1)).obj
        (stageOneWeakObj C X).obj⟩ : StageWeakCategory C 0) =
    (stageWeakDiagonalZeroVertex C : ComposableArrows (StageWeakCategory C 0) 0)
  exact congrArg (fun A : StageWeakCategory C 0 => ComposableArrows.mk₀ A)
    (stageOneWeakObj_reindex_d1 C X)

/-- The target face of the weak-equivalence simplex is the diagonal zero
vertex. -/
theorem stageWeakDiagonalWeakEquivalenceSimplex_d0
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalWeakEquivalenceSimplex C f hf) =
      stageWeakDiagonalZeroVertex C := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalWeakEquivalenceSimplex C f hf) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 0).op
      (stageWeakDiagonalWeakEquivalenceSimplex C f hf) =
      (CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋0⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 1)).map
          (SimplexCategory.δ 0).op)
          (ComposableArrows.mk₁ (stageOneWeakMap C f hf))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 1)).map
        (SimplexCategory.δ 0).op)
        (ComposableArrows.mk₁ (stageOneWeakMap C f hf)) =
      ComposableArrows.mk₀ (stageOneWeakObj C Y) := by
    apply ComposableArrows.ext₀
    rfl
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₀]
  change ComposableArrows.mk₀
      (⟨(reindexStage (C := C) (SimplexCategory.δ 0)).obj
        (stageOneWeakObj C Y).obj⟩ : StageWeakCategory C 0) =
    (stageWeakDiagonalZeroVertex C : ComposableArrows (StageWeakCategory C 0) 0)
  exact congrArg (fun A : StageWeakCategory C 0 => ComposableArrows.mk₀ A)
    (stageOneWeakObj_reindex_d0 C Y)

/-- Based diagonal edge induced by a weak equivalence. -/
noncomputable def stageWeakDiagonalWeakEquivalenceEdge
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (stageWeakDiagonal C).Edge (stageWeakDiagonalZeroVertex C)
      (stageWeakDiagonalZeroVertex C) :=
  SSet.Edge.ofEq
    (SSet.Edge.mk' (stageWeakDiagonalWeakEquivalenceSimplex C f hf))
    (stageWeakDiagonalWeakEquivalenceSimplex_d1 C f hf)
    (stageWeakDiagonalWeakEquivalenceSimplex_d0 C f hf)

@[simp]
theorem stageWeakDiagonalWeakEquivalenceEdge_edge
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (stageWeakDiagonalWeakEquivalenceEdge C f hf).edge =
      ComposableArrows.mk₁ (stageOneWeakMap C f hf) :=
  rfl

/-- The actual zero-vertex degeneracy is the identity on the original reindexed zero stage. -/
@[simp]
theorem stageWeakDiagonalZeroVertex_degeneracy :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C 0)).obj (op ⦋0⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).σ (0 : Fin 1)))
      (stageWeakDiagonalZeroVertex C) =
      ComposableArrows.mk₁
        (𝟙 ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
          (⟨stageZero C⟩ : StageWeakCategory C 0))) := by
  change (stageWeakDiagonal C).map (SimplexCategory.σ (0 : Fin 1)).op
      (stageWeakDiagonalZeroVertex C) = _
  rw [stageWeakDiagonal_map]
  change (CategoryTheory.nerveMap
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)))).app (op ⦋1⦌)
      (((CategoryTheory.nerve (StageWeakCategory C 0)).map
        (SimplexCategory.σ (0 : Fin 1)).op)
        (ComposableArrows.mk₀
          (⟨stageZero C⟩ : StageWeakCategory C 0))) = _
  have hInner :
      ((CategoryTheory.nerve (StageWeakCategory C 0)).map
        (SimplexCategory.σ (0 : Fin 1)).op)
        (ComposableArrows.mk₀
          (⟨stageZero C⟩ : StageWeakCategory C 0)) =
      ComposableArrows.mk₁
        (𝟙 (⟨stageZero C⟩ : StageWeakCategory C 0)) :=
    CategoryTheory.nerve.σ₀_mk₀_eq _
  rw [hInner, CategoryTheory.nerveMap_app_mk₁, Functor.map_id]

/-- The identity edge at the diagonal zero vertex is the identity on the
original degree-one Stage obtained by degenerating the zero stage. -/
theorem stageWeakDiagonalZeroEdge_edge :
    (SSet.Edge.id (X := stageWeakDiagonal C)
      (stageWeakDiagonalZeroVertex C)).edge =
      ComposableArrows.mk₁
        (𝟙 ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
          (⟨stageZero C⟩ : StageWeakCategory C 0))) := by
  rw [SSet.Edge.id_edge]
  exact stageWeakDiagonalZeroVertex_degeneracy C

/-- Reindexing a weak stage along a degeneracy and a cancelling face returns
the original object. -/
theorem reindexStageWeak_sigma_delta_obj
    (A : StageWeakCategory C 1) (j : Fin 2) (i : Fin 3)
    (h : SimplexCategory.δ i ≫ SimplexCategory.σ j =
      𝟙 (⦋1⦌ : SimplexCategory)) :
    (reindexStageWeak C (SimplexCategory.δ i)).obj
        ((reindexStageWeak C (SimplexCategory.σ j)).obj A) = A := by
  change ((reindexStageWeak C (SimplexCategory.σ j) ⋙
    reindexStageWeak C (SimplexCategory.δ i)).obj A) = A
  rw [← reindexStageWeak_comp, h, reindexStageWeak_id]
  rfl

/-- Reindexing a weak-stage morphism along a degeneracy and a cancelling
face returns it after the object equalities are made explicit. -/
theorem reindexStageWeak_sigma_delta_map
    {A B : StageWeakCategory C 1} (φ : A ⟶ B)
    (j : Fin 2) (i : Fin 3)
    (h : SimplexCategory.δ i ≫ SimplexCategory.σ j =
      𝟙 (⦋1⦌ : SimplexCategory))
    (hA : (reindexStageWeak C (SimplexCategory.δ i)).obj
        ((reindexStageWeak C (SimplexCategory.σ j)).obj A) = A)
    (hB : (reindexStageWeak C (SimplexCategory.δ i)).obj
        ((reindexStageWeak C (SimplexCategory.σ j)).obj B) = B) :
    (reindexStageWeak C (SimplexCategory.δ i)).map
        ((reindexStageWeak C (SimplexCategory.σ j)).map φ) =
      eqToHom hA ≫ φ ≫ eqToHom hB.symm := by
  change ((reindexStageWeak C (SimplexCategory.σ j) ⋙
    reindexStageWeak C (SimplexCategory.δ i)).map φ) = _
  have hF : reindexStageWeak C (SimplexCategory.σ j) ⋙
      reindexStageWeak C (SimplexCategory.δ i) =
        𝟭 (StageWeakCategory C 1) := by
    rw [← reindexStageWeak_comp, h, reindexStageWeak_id]
  calc
    _ = eqToHom (Functor.congr_obj hF A) ≫
        (𝟭 (StageWeakCategory C 1)).map φ ≫
          eqToHom (Functor.congr_obj hF B).symm :=
      Functor.congr_hom hF φ
    _ = eqToHom hA ≫ φ ≫ eqToHom hB.symm := by
      have hEqA : Functor.congr_obj hF A = hA := Subsingleton.elim _ _
      have hEqB : Functor.congr_obj hF B = hB := Subsingleton.elim _ _
      rw [hEqA, hEqB]
      rfl

/-- The collapsed `σ₁`/`δ₀` face of an object stage is the degenerated zero
stage. -/
theorem stageOneWeakObj_reindex_sigmaOne_d0 (W : C) :
    (reindexStageWeak C (SimplexCategory.δ (0 : Fin 3))).obj
        ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).obj
          (stageOneWeakObj C W)) =
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
        (⟨stageZero C⟩ : StageWeakCategory C 0) := by
  have hconst :
      SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (0 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    ext i
    fin_cases i <;> rfl
  change ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2)) ⋙
    reindexStageWeak C (SimplexCategory.δ (0 : Fin 3))).obj
      (stageOneWeakObj C W)) = _
  rw [← reindexStageWeak_comp, hconst, reindexStageWeak_comp]
  change (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
      (⟨(reindexStage (C := C) (SimplexCategory.δ (0 : Fin 2))).obj
        (stageOneWeakObj C W).obj⟩ : StageWeakCategory C 0) =
    (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
      (⟨stageZero C⟩ : StageWeakCategory C 0)
  exact congrArg
    (fun A : StageWeakCategory C 0 =>
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj A)
    (stageOneWeakObj_reindex_d0 C W)

/-- The collapsed `σ₀`/`δ₂` face of an object stage is the degenerated zero
stage. -/
theorem stageOneWeakObj_reindex_sigmaZero_d2 (W : C) :
    (reindexStageWeak C (SimplexCategory.δ (2 : Fin 3))).obj
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).obj
          (stageOneWeakObj C W)) =
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
        (⟨stageZero C⟩ : StageWeakCategory C 0) := by
  have hconst :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
        SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    apply SimplexCategory.Hom.ext
    ext i
    fin_cases i <;> rfl
  change ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2)) ⋙
    reindexStageWeak C (SimplexCategory.δ (2 : Fin 3))).obj
      (stageOneWeakObj C W)) = _
  rw [← reindexStageWeak_comp, hconst, reindexStageWeak_comp]
  change (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
      (⟨(reindexStage (C := C) (SimplexCategory.δ (1 : Fin 2))).obj
        (stageOneWeakObj C W).obj⟩ : StageWeakCategory C 0) =
    (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
      (⟨stageZero C⟩ : StageWeakCategory C 0)
  exact congrArg
    (fun A : StageWeakCategory C 0 =>
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj A)
    (stageOneWeakObj_reindex_d1 C W)

/-- Mixed source degeneracy: object edge of `X`, then the zero edge, composes
to the weak-equivalence edge. -/
noncomputable def stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (stageWeakDiagonal C).obj (op ⦋2⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₂
    (𝟙 ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).obj
      (stageOneWeakObj C X)))
    ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).map
      (stageOneWeakMap C f hf))

@[simp]
theorem stageWeakDiagonalWeakEquivalenceSourceTriangle_d2
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 2))
        (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf) =
      (stageWeakDiagonalObjectEdge C X).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 2).op
      (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf) =
      (CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.δ 2))).app (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 2)).map
          (SimplexCategory.δ 2).op)
          (ComposableArrows.mk₂
            (𝟙 ((reindexStageWeak C
              (SimplexCategory.σ (1 : Fin 2))).obj (stageOneWeakObj C X)))
            ((reindexStageWeak C
              (SimplexCategory.σ (1 : Fin 2))).map
                (stageOneWeakMap C f hf)))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 2).op)
        (ComposableArrows.mk₂
          (𝟙 ((reindexStageWeak C
            (SimplexCategory.σ (1 : Fin 2))).obj (stageOneWeakObj C X)))
          ((reindexStageWeak C
            (SimplexCategory.σ (1 : Fin 2))).map
              (stageOneWeakMap C f hf))) =
      ComposableArrows.mk₁
        (𝟙 ((reindexStageWeak C
          (SimplexCategory.σ (1 : Fin 2))).obj
            (stageOneWeakObj C X))) :=
    CategoryTheory.nerve.δ₂_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁, Functor.map_id]
  have hδσ :
      SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
        𝟙 (⦋1⦌ : SimplexCategory) := by
    simpa using SimplexCategory.δ_comp_σ_succ
      (n := 1) (i := (1 : Fin 2))
  rw [reindexStageWeak_sigma_delta_obj C (stageOneWeakObj C X) 1 2 hδσ,
    stageWeakDiagonalObjectEdge_edge]

@[simp]
theorem stageWeakDiagonalWeakEquivalenceSourceTriangle_d1
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 1))
        (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf) =
      (stageWeakDiagonalWeakEquivalenceEdge C f hf).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 1).op
      (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf) =
      (CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 2)).map
          (SimplexCategory.δ 1).op)
          (ComposableArrows.mk₂
            (𝟙 ((reindexStageWeak C
              (SimplexCategory.σ (1 : Fin 2))).obj (stageOneWeakObj C X)))
            ((reindexStageWeak C
              (SimplexCategory.σ (1 : Fin 2))).map
                (stageOneWeakMap C f hf)))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 1).op)
        (ComposableArrows.mk₂
          (𝟙 ((reindexStageWeak C
            (SimplexCategory.σ (1 : Fin 2))).obj (stageOneWeakObj C X)))
          ((reindexStageWeak C
            (SimplexCategory.σ (1 : Fin 2))).map
              (stageOneWeakMap C f hf))) =
      ComposableArrows.mk₁
        ((𝟙 ((reindexStageWeak C
          (SimplexCategory.σ (1 : Fin 2))).obj
            (stageOneWeakObj C X))) ≫
          (reindexStageWeak C
            (SimplexCategory.σ (1 : Fin 2))).map
              (stageOneWeakMap C f hf)) :=
    CategoryTheory.nerve.δ₁_mk₂_eq _ _
  rw [hstep, hface, Category.id_comp,
    CategoryTheory.nerveMap_app_mk₁]
  have hδσ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
        𝟙 (⦋1⦌ : SimplexCategory) := by
    simpa using SimplexCategory.δ_comp_σ_self
      (n := 1) (i := (1 : Fin 2))
  rw [stageWeakDiagonalWeakEquivalenceEdge_edge]
  have hX := reindexStageWeak_sigma_delta_obj C
    (stageOneWeakObj C X) 1 1 hδσ
  have hY := reindexStageWeak_sigma_delta_obj C
    (stageOneWeakObj C Y) 1 1 hδσ
  exact ComposableArrows.ext₁ hX hY
    (reindexStageWeak_sigma_delta_map C (stageOneWeakMap C f hf)
      1 1 hδσ hX hY)

@[simp]
theorem stageWeakDiagonalWeakEquivalenceSourceTriangle_d0
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 0))
        (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf) =
      (SSet.Edge.id (X := stageWeakDiagonal C)
        (stageWeakDiagonalZeroVertex C)).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 0).op
      (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf) =
      (CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 2)).map
          (SimplexCategory.δ 0).op)
          (ComposableArrows.mk₂
            (𝟙 ((reindexStageWeak C
              (SimplexCategory.σ (1 : Fin 2))).obj (stageOneWeakObj C X)))
            ((reindexStageWeak C
              (SimplexCategory.σ (1 : Fin 2))).map
                (stageOneWeakMap C f hf)))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 0).op)
        (ComposableArrows.mk₂
          (𝟙 ((reindexStageWeak C
            (SimplexCategory.σ (1 : Fin 2))).obj (stageOneWeakObj C X)))
          ((reindexStageWeak C
            (SimplexCategory.σ (1 : Fin 2))).map
              (stageOneWeakMap C f hf))) =
      ComposableArrows.mk₁
        ((reindexStageWeak C
          (SimplexCategory.σ (1 : Fin 2))).map
            (stageOneWeakMap C f hf)) :=
    CategoryTheory.nerve.δ₀_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁,
    stageWeakDiagonalZeroEdge_edge]
  have hX := stageOneWeakObj_reindex_sigmaOne_d0 C X
  have hY := stageOneWeakObj_reindex_sigmaOne_d0 C Y
  refine ComposableArrows.ext₁ hX hY ?_
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  ext A
  apply IsZero.eq_of_src
  have hZero : IsZero
      (((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
        (⟨stageZero C⟩ : StageWeakCategory C 0)).obj.obj.obj A) := by
    change IsZero ((zeroDiagram C 0).obj
      ((indexFunctor (SimplexCategory.σ (0 : Fin 1))).obj A))
    exact isZero_zero C
  have hObj := congrArg
    (fun S : StageWeakCategory C 1 => S.obj.obj.obj A) hX
  exact hObj.symm ▸ hZero

/-- The source mixed-degeneracy triangle, oriented
`objectEdge X ; id = weakEdge f`. -/
noncomputable def stageWeakDiagonalWeakEquivalenceSourceCompStruct
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    SSet.Edge.CompStruct (stageWeakDiagonalObjectEdge C X)
      (SSet.Edge.id (stageWeakDiagonalZeroVertex C))
      (stageWeakDiagonalWeakEquivalenceEdge C f hf) :=
  SSet.Edge.CompStruct.mk
    (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf)
    (stageWeakDiagonalWeakEquivalenceSourceTriangle_d2 C f hf)
    (stageWeakDiagonalWeakEquivalenceSourceTriangle_d0 C f hf)
    (stageWeakDiagonalWeakEquivalenceSourceTriangle_d1 C f hf)

/-- Mixed target degeneracy: the zero edge, then the object edge of `Y`,
composes to the weak-equivalence edge. -/
noncomputable def stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (stageWeakDiagonal C).obj (op ⦋2⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₂
    ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).map
      (stageOneWeakMap C f hf))
    (𝟙 ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).obj
      (stageOneWeakObj C Y)))

@[simp]
theorem stageWeakDiagonalWeakEquivalenceTargetTriangle_d2
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 2))
        (stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf) =
      (SSet.Edge.id (X := stageWeakDiagonal C)
        (stageWeakDiagonalZeroVertex C)).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 2).op
      (stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf) =
      (CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.δ 2))).app (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 2)).map
          (SimplexCategory.δ 2).op)
          (ComposableArrows.mk₂
            ((reindexStageWeak C
              (SimplexCategory.σ (0 : Fin 2))).map
                (stageOneWeakMap C f hf))
            (𝟙 ((reindexStageWeak C
              (SimplexCategory.σ (0 : Fin 2))).obj
                (stageOneWeakObj C Y))))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 2).op)
        (ComposableArrows.mk₂
          ((reindexStageWeak C
            (SimplexCategory.σ (0 : Fin 2))).map
              (stageOneWeakMap C f hf))
          (𝟙 ((reindexStageWeak C
            (SimplexCategory.σ (0 : Fin 2))).obj
              (stageOneWeakObj C Y)))) =
      ComposableArrows.mk₁
        ((reindexStageWeak C
          (SimplexCategory.σ (0 : Fin 2))).map
            (stageOneWeakMap C f hf)) :=
    CategoryTheory.nerve.δ₂_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁,
    stageWeakDiagonalZeroEdge_edge]
  have hX := stageOneWeakObj_reindex_sigmaZero_d2 C X
  have hY := stageOneWeakObj_reindex_sigmaZero_d2 C Y
  refine ComposableArrows.ext₁ hX hY ?_
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  ext A
  apply IsZero.eq_of_src
  have hZero : IsZero
      (((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
        (⟨stageZero C⟩ : StageWeakCategory C 0)).obj.obj.obj A) := by
    change IsZero ((zeroDiagram C 0).obj
      ((indexFunctor (SimplexCategory.σ (0 : Fin 1))).obj A))
    exact isZero_zero C
  have hObj := congrArg
    (fun S : StageWeakCategory C 1 => S.obj.obj.obj A) hX
  exact hObj.symm ▸ hZero

@[simp]
theorem stageWeakDiagonalWeakEquivalenceTargetTriangle_d0
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 0))
        (stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf) =
      (stageWeakDiagonalObjectEdge C Y).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 0).op
      (stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf) =
      (CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 2)).map
          (SimplexCategory.δ 0).op)
          (ComposableArrows.mk₂
            ((reindexStageWeak C
              (SimplexCategory.σ (0 : Fin 2))).map
                (stageOneWeakMap C f hf))
            (𝟙 ((reindexStageWeak C
              (SimplexCategory.σ (0 : Fin 2))).obj
                (stageOneWeakObj C Y))))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 0).op)
        (ComposableArrows.mk₂
          ((reindexStageWeak C
            (SimplexCategory.σ (0 : Fin 2))).map
              (stageOneWeakMap C f hf))
          (𝟙 ((reindexStageWeak C
            (SimplexCategory.σ (0 : Fin 2))).obj
              (stageOneWeakObj C Y)))) =
      ComposableArrows.mk₁
        (𝟙 ((reindexStageWeak C
          (SimplexCategory.σ (0 : Fin 2))).obj
            (stageOneWeakObj C Y))) :=
    CategoryTheory.nerve.δ₀_mk₂_eq _ _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁, Functor.map_id]
  have hδσ :
      SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
        𝟙 (⦋1⦌ : SimplexCategory) := by
    simpa using SimplexCategory.δ_comp_σ_self
      (n := 1) (i := (0 : Fin 2))
  rw [reindexStageWeak_sigma_delta_obj C (stageOneWeakObj C Y) 0 0 hδσ,
    stageWeakDiagonalObjectEdge_edge]

@[simp]
theorem stageWeakDiagonalWeakEquivalenceTargetTriangle_d1
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 1))
        (stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf) =
      (stageWeakDiagonalWeakEquivalenceEdge C f hf).edge := by
  change (stageWeakDiagonal C).map _
    (stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 1).op
      (stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf) =
      (CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 2)).map
          (SimplexCategory.δ 1).op)
          (ComposableArrows.mk₂
            ((reindexStageWeak C
              (SimplexCategory.σ (0 : Fin 2))).map
                (stageOneWeakMap C f hf))
            (𝟙 ((reindexStageWeak C
              (SimplexCategory.σ (0 : Fin 2))).obj
                (stageOneWeakObj C Y))))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 1).op)
        (ComposableArrows.mk₂
          ((reindexStageWeak C
            (SimplexCategory.σ (0 : Fin 2))).map
              (stageOneWeakMap C f hf))
          (𝟙 ((reindexStageWeak C
            (SimplexCategory.σ (0 : Fin 2))).obj
              (stageOneWeakObj C Y)))) =
      ComposableArrows.mk₁
        (((reindexStageWeak C
          (SimplexCategory.σ (0 : Fin 2))).map
            (stageOneWeakMap C f hf)) ≫
          𝟙 ((reindexStageWeak C
            (SimplexCategory.σ (0 : Fin 2))).obj
              (stageOneWeakObj C Y))) :=
    CategoryTheory.nerve.δ₁_mk₂_eq _ _
  rw [hstep, hface, Category.comp_id,
    CategoryTheory.nerveMap_app_mk₁]
  have hδσ :
      SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
        𝟙 (⦋1⦌ : SimplexCategory) := by
    simpa using SimplexCategory.δ_comp_σ_succ
      (n := 1) (i := (0 : Fin 2))
  rw [stageWeakDiagonalWeakEquivalenceEdge_edge]
  have hX := reindexStageWeak_sigma_delta_obj C
    (stageOneWeakObj C X) 0 1 hδσ
  have hY := reindexStageWeak_sigma_delta_obj C
    (stageOneWeakObj C Y) 0 1 hδσ
  exact ComposableArrows.ext₁ hX hY
    (reindexStageWeak_sigma_delta_map C (stageOneWeakMap C f hf)
      0 1 hδσ hX hY)

/-- The target mixed-degeneracy triangle, oriented
`id ; objectEdge Y = weakEdge f`. -/
noncomputable def stageWeakDiagonalWeakEquivalenceTargetCompStruct
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    SSet.Edge.CompStruct
      (SSet.Edge.id (stageWeakDiagonalZeroVertex C))
      (stageWeakDiagonalObjectEdge C Y)
      (stageWeakDiagonalWeakEquivalenceEdge C f hf) :=
  SSet.Edge.CompStruct.mk
    (stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf)
    (stageWeakDiagonalWeakEquivalenceTargetTriangle_d2 C f hf)
    (stageWeakDiagonalWeakEquivalenceTargetTriangle_d0 C f hf)
    (stageWeakDiagonalWeakEquivalenceTargetTriangle_d1 C f hf)

/-- Weakly equivalent objects determine the same canonical morphism in the
fundamental groupoid of the weak-stage diagonal. -/
theorem stageWeakDiagonalObjectEdge_homMk_eq_of_weakEquivalence
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    SSet.FundamentalGroupoid.homMk (stageWeakDiagonalObjectEdge C X) =
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalObjectEdge C Y) := by
  have hX :=
    (stageWeakDiagonalWeakEquivalenceSourceCompStruct C f hf).homMk_comp
  rw [SSet.FundamentalGroupoid.homMk_id, Category.comp_id] at hX
  have hY :=
    (stageWeakDiagonalWeakEquivalenceTargetCompStruct C f hf).homMk_comp
  rw [SSet.FundamentalGroupoid.homMk_id, Category.id_comp] at hY
  exact hX.trans hY.symm

end CategoryTheory.Waldhausen.SConstruction

end
