/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalConnected
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0WeakEquivalence
import Mathlib.Tactic.FinCases

/-!
# Coherent Stage-zero contraction in the weak-stage diagonal

Every degree-zero Stage is pointwise zero.  Consequently its weak-stage
category is thin and every object is canonically isomorphic to the zero
Stage.  The resulting natural contraction gives coherent zero-to-vertex
edges in the weak-stage diagonal.  A degree-two simplex records naturality
of those connectors under every Stage-zero morphism.

This file contains no Stage-one counit or arbitrary-edge normalization, and
makes no realization, K-zero, additivity, spectrum, or Q/S claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial ZeroObject
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

set_option linter.defProp false in
@[no_expose]
def arZero_eq_diag (I : Ar 0) : I = diag (0 : Fin 1) := by
  obtain ⟨i, j, f, rfl⟩ := Arrow.mk_surjective I
  fin_cases i
  fin_cases j
  rfl

/-- Any two parallel morphisms between degree-zero weak stages are equal. -/
theorem stageWeakZero_hom_ext {S T : StageWeakCategory C 0}
    (f g : S ⟶ T) : f = g := by
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  ext I
  have hI := arZero_eq_diag I
  subst I
  exact (S.obj.property.diag_isZero 0).eq_of_src _ _

/-- The degree-zero weak-stage category is thin. -/
instance stageWeakZero_isThin : Quiver.IsThin (StageWeakCategory C 0) :=
  fun _ _ => ⟨stageWeakZero_hom_ext C⟩

/-- Canonical weak-stage isomorphism from the zero Stage to an arbitrary
degree-zero Stage. -/
noncomputable def stageWeakZeroIso (T : StageWeakCategory C 0) :
    (⟨stageZero C⟩ : StageWeakCategory C 0) ≅ T := by
  let e : stageZero C ≅ T.obj := by
    refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun I => ?_) ?_)
    · have hI := arZero_eq_diag I
      subst I
      exact (isZero_zero C).iso (T.obj.property.diag_isZero 0)
    · intro I J f
      have hJ := arZero_eq_diag J
      subst J
      exact (T.obj.property.diag_isZero 0).eq_of_tgt _ _
  exact WideSubcategory.isoMk e
    ((stageWeak C 0).of_isIso e.hom)
    ((stageWeak C 0).of_isIso e.inv)

/-- Natural contraction of the degree-zero weak-stage category to its zero
Stage. -/
noncomputable def stageWeakZeroContraction :
    (Functor.const (StageWeakCategory C 0)).obj
        (⟨stageZero C⟩ : StageWeakCategory C 0) ≅
      𝟭 (StageWeakCategory C 0) :=
  NatIso.ofComponents (stageWeakZeroIso C)
    (fun _ => Subsingleton.elim _ _)

@[simp]
theorem stageWeakZeroContraction_hom_app
    (T : StageWeakCategory C 0) :
    (stageWeakZeroContraction C).hom.app T = (stageWeakZeroIso C T).hom :=
  rfl

/-- Naturality of the canonical zero-to-object morphisms. -/
@[reassoc]
theorem stageWeakZeroToObj_naturality
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakZeroIso C S).hom ≫ f = (stageWeakZeroIso C T).hom :=
  by
    simpa using ((stageWeakZeroContraction C).hom.naturality f).symm

/-- Reindexing a Stage-zero object along `σ 0` and either face returns the
original object. -/
theorem reindexStageWeak_sigmaZero_delta_obj
    (T : StageWeakCategory C 0) (i : Fin 2) :
    ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)) ⋙
      reindexStageWeak C (SimplexCategory.δ i)).obj T) = T := by
  fin_cases i
  · change ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)) ⋙
      reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).obj T) = T
    rw [← reindexStageWeak_comp]
    have hδσ : SimplexCategory.δ (0 : Fin 2) ≫
        SimplexCategory.σ (0 : Fin 1) =
        𝟙 (⦋0⦌ : SimplexCategory) := by
      simpa using SimplexCategory.δ_comp_σ_self
        (n := 0) (i := (0 : Fin 1))
    rw [hδσ, reindexStageWeak_id]
    rfl
  · change ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)) ⋙
      reindexStageWeak C (SimplexCategory.δ (1 : Fin 2))).obj T) = T
    rw [← reindexStageWeak_comp]
    have hδσ : SimplexCategory.δ (1 : Fin 2) ≫
        SimplexCategory.σ (0 : Fin 1) =
        𝟙 (⦋0⦌ : SimplexCategory) := by
      simpa using SimplexCategory.δ_comp_σ_succ
        (n := 0) (i := (0 : Fin 1))
    rw [hδσ, reindexStageWeak_id]
    rfl

/-- Underlying diagonal simplex of the canonical zero-to-object connector. -/
noncomputable def stageWeakDiagonalZeroToObjSimplex
    (T : StageWeakCategory C 0) :
    (stageWeakDiagonal C).obj (op ⦋1⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₁
    ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map
      (stageWeakZeroIso C T).hom)

/-- Canonical diagonal connector from the zero vertex to a represented
Stage-zero vertex. -/
noncomputable def stageWeakDiagonalZeroToObjEdge
    (T : StageWeakCategory C 0) :
    (stageWeakDiagonal C).Edge (stageWeakDiagonalZeroVertex C)
      (ComposableArrows.mk₀ T) := by
  let s := stageWeakDiagonalZeroToObjSimplex C T
  refine SSet.Edge.ofEq (SSet.Edge.mk' s) ?_ ?_
  · have hInner :
        ((CategoryTheory.nerve (StageWeakCategory C 1)).map
          (SimplexCategory.δ 1).op) s =
          ComposableArrows.mk₀
            ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
              (⟨stageZero C⟩ : StageWeakCategory C 0)) := by
      apply ComposableArrows.ext₀
      rfl
    have hOuter :
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋0⦌)
          (ComposableArrows.mk₀
            ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
              (⟨stageZero C⟩ : StageWeakCategory C 0))) =
          ComposableArrows.mk₀
            (⟨stageZero C⟩ : StageWeakCategory C 0) := by
      rw [CategoryTheory.nerveMap_app_mk₀]
      exact congrArg ComposableArrows.mk₀
        (reindexStageWeak_sigmaZero_delta_obj C
          (⟨stageZero C⟩ : StageWeakCategory C 0) 1)
    have hMap :
        (stageWeakDiagonal C).map (SimplexCategory.δ (1 : Fin 2)).op s =
          (CategoryTheory.nerveMap
            (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋0⦌)
            (((CategoryTheory.nerve (StageWeakCategory C 1)).map
              (SimplexCategory.δ 1).op) s) := rfl
    change (stageWeakDiagonal C).map
      (SimplexCategory.δ (1 : Fin 2)).op s = _
    rw [hMap, hInner, hOuter]
    rfl
  · have hInner :
        ((CategoryTheory.nerve (StageWeakCategory C 1)).map
          (SimplexCategory.δ 0).op) s =
          ComposableArrows.mk₀
            ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj T) := by
      apply ComposableArrows.ext₀
      rfl
    have hOuter :
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋0⦌)
          (ComposableArrows.mk₀
            ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj T)) =
          ComposableArrows.mk₀ T := by
      rw [CategoryTheory.nerveMap_app_mk₀]
      exact congrArg ComposableArrows.mk₀
        (reindexStageWeak_sigmaZero_delta_obj C T 0)
    have hMap :
        (stageWeakDiagonal C).map (SimplexCategory.δ (0 : Fin 2)).op s =
          (CategoryTheory.nerveMap
            (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋0⦌)
            (((CategoryTheory.nerve (StageWeakCategory C 1)).map
              (SimplexCategory.δ 0).op) s) := rfl
    change (stageWeakDiagonal C).map
      (SimplexCategory.δ (0 : Fin 2)).op s = _
    rw [hMap, hInner, hOuter]
    rfl

@[simp]
theorem stageWeakDiagonalZeroToObjEdge_edge
    (T : StageWeakCategory C 0) :
    (stageWeakDiagonalZeroToObjEdge C T).edge =
      ComposableArrows.mk₁
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map
          (stageWeakZeroIso C T).hom) :=
  rfl

@[simp]
theorem stageWeakDiagonalZeroToObjEdge_src
    (T : StageWeakCategory C 0) :
    (stageWeakDiagonal C).δ 1
        (stageWeakDiagonalZeroToObjEdge C T).edge =
      stageWeakDiagonalZeroVertex C :=
  SSet.Edge.src_eq _

@[simp]
theorem stageWeakDiagonalZeroToObjEdge_tgt
    (T : StageWeakCategory C 0) :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalZeroToObjEdge C T).edge =
      ComposableArrows.mk₀ T :=
  SSet.Edge.tgt_eq _

/-- Canonical connector from the zero vertex to an arbitrary diagonal
vertex. -/
noncomputable def stageWeakDiagonalZeroToVertexEdge
    (x : (stageWeakDiagonal C).obj (op ⦋0⦌)) :
    (stageWeakDiagonal C).Edge (stageWeakDiagonalZeroVertex C) x :=
  (stageWeakDiagonalZeroToObjEdge C (CategoryTheory.nerveEquiv x)).ofEq
    rfl (CategoryTheory.nerveEquiv.left_inv x)

@[simp]
theorem stageWeakDiagonalZeroToVertexEdge_edge
    (x : (stageWeakDiagonal C).obj (op ⦋0⦌)) :
    (stageWeakDiagonalZeroToVertexEdge C x).edge =
      (stageWeakDiagonalZeroToObjEdge C
        (CategoryTheory.nerveEquiv x)).edge :=
  rfl

/-- Underlying diagonal simplex induced by a Stage-zero morphism. -/
noncomputable def stageWeakDiagonalStageZeroMapSimplex
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).obj (op ⦋1⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₁
    ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map f)

/-- Diagonal edge induced by a Stage-zero morphism. -/
noncomputable def stageWeakDiagonalStageZeroMapEdge
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).Edge (ComposableArrows.mk₀ S)
      (ComposableArrows.mk₀ T) := by
  let s := stageWeakDiagonalStageZeroMapSimplex C f
  refine SSet.Edge.ofEq (SSet.Edge.mk' s) ?_ ?_
  · have hInner :
        ((CategoryTheory.nerve (StageWeakCategory C 1)).map
          (SimplexCategory.δ 1).op) s =
          ComposableArrows.mk₀
            ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj S) := by
      apply ComposableArrows.ext₀
      rfl
    have hOuter :
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋0⦌)
          (ComposableArrows.mk₀
            ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj S)) =
          ComposableArrows.mk₀ S := by
      rw [CategoryTheory.nerveMap_app_mk₀]
      exact congrArg ComposableArrows.mk₀
        (reindexStageWeak_sigmaZero_delta_obj C S 1)
    have hMap :
        (stageWeakDiagonal C).map (SimplexCategory.δ (1 : Fin 2)).op s =
          (CategoryTheory.nerveMap
            (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋0⦌)
            (((CategoryTheory.nerve (StageWeakCategory C 1)).map
              (SimplexCategory.δ 1).op) s) := rfl
    change (stageWeakDiagonal C).map
      (SimplexCategory.δ (1 : Fin 2)).op s = _
    rw [hMap, hInner, hOuter]
    rfl
  · have hInner :
        ((CategoryTheory.nerve (StageWeakCategory C 1)).map
          (SimplexCategory.δ 0).op) s =
          ComposableArrows.mk₀
            ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj T) := by
      apply ComposableArrows.ext₀
      rfl
    have hOuter :
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋0⦌)
          (ComposableArrows.mk₀
            ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj T)) =
          ComposableArrows.mk₀ T := by
      rw [CategoryTheory.nerveMap_app_mk₀]
      exact congrArg ComposableArrows.mk₀
        (reindexStageWeak_sigmaZero_delta_obj C T 0)
    have hMap :
        (stageWeakDiagonal C).map (SimplexCategory.δ (0 : Fin 2)).op s =
          (CategoryTheory.nerveMap
            (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋0⦌)
            (((CategoryTheory.nerve (StageWeakCategory C 1)).map
              (SimplexCategory.δ 0).op) s) := rfl
    change (stageWeakDiagonal C).map
      (SimplexCategory.δ (0 : Fin 2)).op s = _
    rw [hMap, hInner, hOuter]
    rfl

@[simp]
theorem stageWeakDiagonalStageZeroMapEdge_edge
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonalStageZeroMapEdge C f).edge =
      ComposableArrows.mk₁
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map f) :=
  rfl

@[simp]
theorem stageWeakDiagonalStageZeroMapEdge_src
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).δ 1
        (stageWeakDiagonalStageZeroMapEdge C f).edge =
      ComposableArrows.mk₀ S :=
  SSet.Edge.src_eq _

@[simp]
theorem stageWeakDiagonalStageZeroMapEdge_tgt
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalStageZeroMapEdge C f).edge =
      ComposableArrows.mk₀ T :=
  SSet.Edge.tgt_eq _

/-- Unique two-step degeneracy from degree two to degree zero. -/
def stageWeakZeroTwoIndex : (⦋2⦌ : SimplexCategory) ⟶ ⦋0⦌ :=
  SimplexCategory.σ (0 : Fin 2) ≫ SimplexCategory.σ (0 : Fin 1)

private theorem delta_comp_stageWeakZeroTwoIndex (i : Fin 3) :
    SimplexCategory.δ i ≫ stageWeakZeroTwoIndex =
      SimplexCategory.σ (0 : Fin 1) := by
  fin_cases i <;>
    apply SimplexCategory.Hom.ext <;>
    ext j <;>
    fin_cases j <;>
    rfl

private theorem reindexStageWeak_zeroTwo_delta_mk₁
    {S T : StageWeakCategory C 0} (f : S ⟶ T) (i : Fin 3) :
    ComposableArrows.mk₁
        ((reindexStageWeak C (SimplexCategory.δ i)).map
          ((reindexStageWeak C stageWeakZeroTwoIndex).map f)) =
      ComposableArrows.mk₁
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map f) := by
  have hF : reindexStageWeak C stageWeakZeroTwoIndex ⋙
      reindexStageWeak C (SimplexCategory.δ i) =
        reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)) := by
    rw [← reindexStageWeak_comp, delta_comp_stageWeakZeroTwoIndex]
  exact ComposableArrows.ext₁
    (Functor.congr_obj hF S) (Functor.congr_obj hF T)
    (Functor.congr_hom hF f)

/-- Degree-two simplex expressing naturality of the Stage-zero connectors. -/
noncomputable def stageWeakDiagonalZeroConnectorSimplex
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).obj (op ⦋2⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₂
    ((reindexStageWeak C stageWeakZeroTwoIndex).map
      (stageWeakZeroIso C S).hom)
    ((reindexStageWeak C stageWeakZeroTwoIndex).map f)

@[simp]
theorem stageWeakDiagonalZeroConnectorSimplex_d2
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).δ 2
        (stageWeakDiagonalZeroConnectorSimplex C f) =
      (stageWeakDiagonalZeroToObjEdge C S).edge := by
  let g₀ := (reindexStageWeak C stageWeakZeroTwoIndex).map
    (stageWeakZeroIso C S).hom
  let g₁ := (reindexStageWeak C stageWeakZeroTwoIndex).map f
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 2).op
          (stageWeakDiagonalZeroConnectorSimplex C f) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 2))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 2).op)
            (ComposableArrows.mk₂ g₀ g₁)) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 2).op) (ComposableArrows.mk₂ g₀ g₁) =
        ComposableArrows.mk₁ g₀ :=
    CategoryTheory.nerve.δ₂_mk₂_eq _ _
  change (stageWeakDiagonal C).map (SimplexCategory.δ 2).op
    (stageWeakDiagonalZeroConnectorSimplex C f) = _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁]
  exact reindexStageWeak_zeroTwo_delta_mk₁ C
    (stageWeakZeroIso C S).hom 2

@[simp]
theorem stageWeakDiagonalZeroConnectorSimplex_d0
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalZeroConnectorSimplex C f) =
      (stageWeakDiagonalStageZeroMapEdge C f).edge := by
  let g₀ := (reindexStageWeak C stageWeakZeroTwoIndex).map
    (stageWeakZeroIso C S).hom
  let g₁ := (reindexStageWeak C stageWeakZeroTwoIndex).map f
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 0).op
          (stageWeakDiagonalZeroConnectorSimplex C f) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 0))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 0).op)
            (ComposableArrows.mk₂ g₀ g₁)) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 0).op) (ComposableArrows.mk₂ g₀ g₁) =
        ComposableArrows.mk₁ g₁ :=
    CategoryTheory.nerve.δ₀_mk₂_eq _ _
  change (stageWeakDiagonal C).map (SimplexCategory.δ 0).op
    (stageWeakDiagonalZeroConnectorSimplex C f) = _
  rw [hstep, hface, CategoryTheory.nerveMap_app_mk₁]
  exact reindexStageWeak_zeroTwo_delta_mk₁ C f 0

@[simp]
theorem stageWeakDiagonalZeroConnectorSimplex_d1
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).δ 1
        (stageWeakDiagonalZeroConnectorSimplex C f) =
      (stageWeakDiagonalZeroToObjEdge C T).edge := by
  let g₀ := (reindexStageWeak C stageWeakZeroTwoIndex).map
    (stageWeakZeroIso C S).hom
  let g₁ := (reindexStageWeak C stageWeakZeroTwoIndex).map f
  have hstep :
      (stageWeakDiagonal C).map (SimplexCategory.δ 1).op
          (stageWeakDiagonalZeroConnectorSimplex C f) =
        (CategoryTheory.nerveMap
          (reindexStageWeak C (SimplexCategory.δ 1))).app (op ⦋1⦌)
          (((CategoryTheory.nerve (StageWeakCategory C 2)).map
            (SimplexCategory.δ 1).op)
            (ComposableArrows.mk₂ g₀ g₁)) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 1).op) (ComposableArrows.mk₂ g₀ g₁) =
        ComposableArrows.mk₁ (g₀ ≫ g₁) :=
    CategoryTheory.nerve.δ₁_mk₂_eq _ _
  change (stageWeakDiagonal C).map (SimplexCategory.δ 1).op
    (stageWeakDiagonalZeroConnectorSimplex C f) = _
  rw [hstep, hface, ← Functor.map_comp,
    stageWeakZeroToObj_naturality,
    CategoryTheory.nerveMap_app_mk₁]
  exact reindexStageWeak_zeroTwo_delta_mk₁ C
    (stageWeakZeroIso C T).hom 1

/-- Naturality triangle for the coherent Stage-zero connectors. -/
noncomputable def stageWeakDiagonalZeroConnectorCompStruct
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    SSet.Edge.CompStruct
      (stageWeakDiagonalZeroToObjEdge C S)
      (stageWeakDiagonalStageZeroMapEdge C f)
      (stageWeakDiagonalZeroToObjEdge C T) :=
  SSet.Edge.CompStruct.mk
    (stageWeakDiagonalZeroConnectorSimplex C f)
    (stageWeakDiagonalZeroConnectorSimplex_d2 C f)
    (stageWeakDiagonalZeroConnectorSimplex_d0 C f)
    (stageWeakDiagonalZeroConnectorSimplex_d1 C f)

/-- Fundamental-groupoid form of Stage-zero connector naturality. -/
theorem stageWeakDiagonalZeroConnector_homMk_comp
    {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToObjEdge C S) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageZeroMapEdge C f) =
    SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalZeroToObjEdge C T) :=
  (stageWeakDiagonalZeroConnectorCompStruct C f).homMk_comp

set_option backward.isDefEq.respectTransparency false in
/-- The connector from the zero Stage to itself is the identity edge. -/
theorem stageWeakDiagonalZeroToObjEdge_zero :
    stageWeakDiagonalZeroToObjEdge C
        (⟨stageZero C⟩ : StageWeakCategory C 0) =
      SSet.Edge.id (stageWeakDiagonalZeroVertex C) := by
  apply SSet.Edge.ext
  have hIso : (stageWeakZeroIso C
      (⟨stageZero C⟩ : StageWeakCategory C 0)).hom = 𝟙 _ :=
    Subsingleton.elim _ _
  calc
    (stageWeakDiagonalZeroToObjEdge C
        (⟨stageZero C⟩ : StageWeakCategory C 0)).edge =
      ComposableArrows.mk₁
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map
          (stageWeakZeroIso C
            (⟨stageZero C⟩ : StageWeakCategory C 0)).hom) :=
      stageWeakDiagonalZeroToObjEdge_edge C _
    _ = ComposableArrows.mk₁
        (𝟙 ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
          (⟨stageZero C⟩ : StageWeakCategory C 0))) := by
      rw [hIso, Functor.map_id]
    _ = (SSet.Edge.id (stageWeakDiagonalZeroVertex C)).edge :=
      (stageWeakDiagonalZeroEdge_edge C).symm

set_option backward.isDefEq.respectTransparency false in
/-- The zero-stage connector is the identity in the simplicial fundamental
groupoid. -/
theorem stageWeakDiagonalZeroToObjEdge_zero_homMk :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToObjEdge C
          (⟨stageZero C⟩ : StageWeakCategory C 0)) =
      𝟙 _ := by
  simpa only [stageWeakDiagonalZeroToObjEdge_zero] using
    SSet.FundamentalGroupoid.homMk_id (stageWeakDiagonalZeroVertex C)

end CategoryTheory.Waldhausen.SConstruction

end
