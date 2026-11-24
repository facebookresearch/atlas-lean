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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwo
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

/-!
# Converse functor from cofiber sequences to degree-two stages

Object-level converse for the next semantic gate: from
`S : CofiberSequenceCategory C` build `Stage C 2` via committed `stageTwo`,
extracting `X/Y/Z` with `ComposableArrows.obj'`, `f/g` with `map'`, and the
category property as `hSeq`. Morphisms go via `ComposableArrows.app'`: identities
on diagonals and the three sequence components off diagonal, following the
existing `StageOne` functor pattern, then lift through `stageProperty`.

Exposes only the documented functor and object/generating-map computation
lemmas. No inverse, equivalence, reindexing change, nerve, realization,
Q/S comparison, or K/G-theory content.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Diagram-level functor: identities on diagonals, the three sequence
components off diagonal. -/
noncomputable def stageTwoDiagramFunctor : CofiberSequenceCategory C ⥤ (Ar 2 ⥤ C) where
  obj S :=
    stageTwoDiagram C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2)
      (S.obj.map' 0 1) (S.obj.map' 1 2) S.property
  map {S T} φ :=
    NatTrans.mk (fun A => by
      by_cases ha : A.left = A.right
      · have hS : (stageTwoDiagram C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2)
            (S.obj.map' 0 1) (S.obj.map' 1 2) S.property).obj A = (0 : C) := by
          simp [stageTwoDiagram, stageTwoDiagramObj, ha]
        have hT : (stageTwoDiagram C (T.obj.obj' 0) (T.obj.obj' 1) (T.obj.obj' 2)
            (T.obj.map' 0 1) (T.obj.map' 1 2) T.property).obj A = (0 : C) := by
          simp [stageTwoDiagram, stageTwoDiagramObj, ha]
        rw [hS, hT]
        exact 𝟙 (0 : C)
      · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
        · have hS : (stageTwoDiagram C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2)
              (S.obj.map' 0 1) (S.obj.map' 1 2) S.property).obj A =
              S.obj.obj' 0 := by
            simp only [stageTwoDiagram]
            rw [stageTwoDiagramObj_of_01 _ _ _ _ ha ha01]
          have hT : (stageTwoDiagram C (T.obj.obj' 0) (T.obj.obj' 1) (T.obj.obj' 2)
              (T.obj.map' 0 1) (T.obj.map' 1 2) T.property).obj A =
              T.obj.obj' 0 := by
            simp only [stageTwoDiagram]
            rw [stageTwoDiagramObj_of_01 _ _ _ _ ha ha01]
          rw [hS, hT]
          exact ComposableArrows.app' φ.hom 0
        · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
          · have hS : (stageTwoDiagram C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2)
                (S.obj.map' 0 1) (S.obj.map' 1 2) S.property).obj A =
                S.obj.obj' 1 := by
              simp only [stageTwoDiagram]
              rw [stageTwoDiagramObj_of_02 _ _ _ _ ha ha01 ha02]
            have hT : (stageTwoDiagram C (T.obj.obj' 0) (T.obj.obj' 1) (T.obj.obj' 2)
                (T.obj.map' 0 1) (T.obj.map' 1 2) T.property).obj A =
                T.obj.obj' 1 := by
              simp only [stageTwoDiagram]
              rw [stageTwoDiagramObj_of_02 _ _ _ _ ha ha01 ha02]
            rw [hS, hT]
            exact ComposableArrows.app' φ.hom 1
          · have hS : (stageTwoDiagram C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2)
                (S.obj.map' 0 1) (S.obj.map' 1 2) S.property).obj A =
                S.obj.obj' 2 := by
              simp only [stageTwoDiagram]
              rw [stageTwoDiagramObj_of_12 _ _ _ _ ha ha01 ha02]
            have hT : (stageTwoDiagram C (T.obj.obj' 0) (T.obj.obj' 1) (T.obj.obj' 2)
                (T.obj.map' 0 1) (T.obj.map' 1 2) T.property).obj A =
                T.obj.obj' 2 := by
              simp only [stageTwoDiagram]
              rw [stageTwoDiagramObj_of_12 _ _ _ _ ha ha01 ha02]
            rw [hS, hT]
            exact ComposableArrows.app' φ.hom 2) (fun {A B} f => by
      by_cases ha : A.left = A.right
      · have hASrc : (stageTwoDiagram C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2)
            (S.obj.map' 0 1) (S.obj.map' 1 2) S.property).obj A = (0 : C) := by
          simp [stageTwoDiagram, stageTwoDiagramObj, ha]
        have hZ : IsZero ((stageTwoDiagram C (S.obj.obj' 0) (S.obj.obj' 1)
            (S.obj.obj' 2) (S.obj.map' 0 1) (S.obj.map' 1 2) S.property).obj A) :=
          hASrc.symm ▸ isZero_zero C
        exact hZ.eq_of_src _ _
      · by_cases hb : B.left = B.right
        · have hBTgt : (stageTwoDiagram C (T.obj.obj' 0) (T.obj.obj' 1) (T.obj.obj' 2)
              (T.obj.map' 0 1) (T.obj.map' 1 2) T.property).obj B = (0 : C) := by
            simp [stageTwoDiagram, stageTwoDiagramObj, hb]
          have hZ : IsZero ((stageTwoDiagram C (T.obj.obj' 0) (T.obj.obj' 1)
              (T.obj.obj' 2) (T.obj.map' 0 1) (T.obj.map' 1 2) T.property).obj B) :=
            hBTgt.symm ▸ isZero_zero C
          exact hZ.eq_of_tgt _ _
        · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
          · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
            · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                stageTwo_ar2_eq_interval01 ha01
              have hB : B = interval (0 : Fin 3) 1 (by decide) :=
                stageTwo_ar2_eq_interval01 hb01
              subst hA
              subst hB
              have hf : f = 𝟙 _ :=
                Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
              subst hf
              simp [stageTwoDiagram, Category.id_comp, Category.comp_id]
            · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
              · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 ha01
                have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval02 hb02
                subst hA
                subst hB
                exact ComposableArrows.naturality' φ.hom 0 1
              · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 ha01
                have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval12 hb hb01 hb02
                subst hA
                subst hB
                have h01 := ComposableArrows.naturality' φ.hom 0 1
                  (Nat.zero_le 1) (Nat.le_succ 1)
                have h12 := ComposableArrows.naturality' φ.hom 1 2
                  (Nat.le_succ 1) le_rfl
                calc (S.obj.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫
                        S.obj.map' 1 2 (Nat.le_succ 1) le_rfl) ≫
                        ComposableArrows.app' φ.hom 2 le_rfl
                    = S.obj.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫
                        (S.obj.map' 1 2 (Nat.le_succ 1) le_rfl ≫
                          ComposableArrows.app' φ.hom 2 le_rfl) := by
                      rw [Category.assoc]
                    _ = S.obj.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫
                        (ComposableArrows.app' φ.hom 1 (Nat.le_succ 1) ≫
                          T.obj.map' 1 2 (Nat.le_succ 1) le_rfl) := by
                      rw [h12]
                    _ = (S.obj.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫
                          ComposableArrows.app' φ.hom 1 (Nat.le_succ 1)) ≫
                        T.obj.map' 1 2 (Nat.le_succ 1) le_rfl := by
                      rw [← Category.assoc]
                    _ = (ComposableArrows.app' φ.hom 0 (Nat.zero_le 2) ≫
                          T.obj.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1)) ≫
                        T.obj.map' 1 2 (Nat.le_succ 1) le_rfl := by
                      rw [h01]
                    _ = ComposableArrows.app' φ.hom 0 (Nat.zero_le 2) ≫
                        (T.obj.map' 0 1 (Nat.zero_le 1) (Nat.le_succ 1) ≫
                          T.obj.map' 1 2 (Nat.le_succ 1) le_rfl) := by
                      rw [Category.assoc]
          · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
            · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
              · exfalso
                have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval02 ha02
                have hB : B = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 hb01
                subst hA
                subst hB
                have hle : (2 : Fin 3) ≤ (1 : Fin 3) := leOfHom f.right
                exact absurd hle (by decide)
              · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
                · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval02 ha02
                  have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval02 hb02
                  subst hA
                  subst hB
                  have hf : f = 𝟙 _ :=
                    Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
                  subst hf
                  simp [stageTwoDiagram, Category.id_comp, Category.comp_id]
                · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval02 ha02
                  have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval12 hb hb01 hb02
                  subst hA
                  subst hB
                  exact ComposableArrows.naturality' φ.hom 1 2
            · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
              · exfalso
                have hA : A = interval (1 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval12 ha ha01 ha02
                have hB : B = interval (0 : Fin 3) 1 (by decide) :=
                  stageTwo_ar2_eq_interval01 hb01
                subst hA
                subst hB
                have hleL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom f.left
                exact absurd hleL (by decide)
              · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
                · exfalso
                  have hA : A = interval (1 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval12 ha ha01 ha02
                  have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval02 hb02
                  subst hA
                  subst hB
                  have hleL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom f.left
                  exact absurd hleL (by decide)
                · have hA : A = interval (1 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval12 ha ha01 ha02
                  have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                    stageTwo_ar2_eq_interval12 hb hb01 hb02
                  subst hA
                  subst hB
                  have hf : f = 𝟙 _ :=
                    Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
                  subst hf
                  simp [stageTwoDiagram, Category.id_comp, Category.comp_id])
  map_id S := by
    ext A
    by_cases ha : A.left = A.right
    · have hObj : (stageTwoDiagram C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2)
          (S.obj.map' 0 1) (S.obj.map' 1 2) S.property).obj A = (0 : C) := by
        simp [stageTwoDiagram, stageTwoDiagramObj, ha]
      have hZ : IsZero ((stageTwoDiagram C (S.obj.obj' 0) (S.obj.obj' 1)
          (S.obj.obj' 2) (S.obj.map' 0 1) (S.obj.map' 1 2) S.property).obj A) :=
        hObj.symm ▸ isZero_zero C
      exact hZ.eq_of_src _ _
    · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
      · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
          stageTwo_ar2_eq_interval01 ha01
        subst hA
        rfl
      · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
        · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
            stageTwo_ar2_eq_interval02 ha02
          subst hA
          rfl
        · have hA : A = interval (1 : Fin 3) 2 (by decide) :=
            stageTwo_ar2_eq_interval12 ha ha01 ha02
          subst hA
          rfl
  map_comp {R S T} φ ψ := by
    ext A
    by_cases ha : A.left = A.right
    · have hObj : (stageTwoDiagram C (R.obj.obj' 0) (R.obj.obj' 1) (R.obj.obj' 2)
          (R.obj.map' 0 1) (R.obj.map' 1 2) R.property).obj A = (0 : C) := by
        simp [stageTwoDiagram, stageTwoDiagramObj, ha]
      have hZ : IsZero ((stageTwoDiagram C (R.obj.obj' 0) (R.obj.obj' 1)
          (R.obj.obj' 2) (R.obj.map' 0 1) (R.obj.map' 1 2) R.property).obj A) :=
        hObj.symm ▸ isZero_zero C
      exact hZ.eq_of_src _ _
    · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
      · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
          stageTwo_ar2_eq_interval01 ha01
        subst hA
        rfl
      · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
        · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
            stageTwo_ar2_eq_interval02 ha02
          subst hA
          rfl
        · have hA : A = interval (1 : Fin 3) 2 (by decide) :=
            stageTwo_ar2_eq_interval12 ha ha01 ha02
          subst hA
          rfl

/-- Converse functor from cofiber sequences to degree-two stages. -/
noncomputable def stageTwoFunctor : CofiberSequenceCategory C ⥤ Stage C 2 :=
  (stageProperty C 2).lift (stageTwoDiagramFunctor C)
    (fun S => isStage_stageTwoDiagram C _ _ _ _ _ S.property)

/-- The functor sends every diagonal to the chosen zero object. -/
theorem stageTwoFunctor_obj_diag (S : CofiberSequenceCategory C) (i : Fin 3) :
    ((stageTwoFunctor C).obj S).obj.obj (diag i) = (0 : C) :=
  stageTwoDiagramObj_diag C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2) i

/-- The functor sends `(0,1)` to the first component. -/
theorem stageTwoFunctor_obj_01 (S : CofiberSequenceCategory C) (h : (0 : Fin 3) ≤ 1) :
    ((stageTwoFunctor C).obj S).obj.obj (interval 0 1 h) = S.obj.obj' 0 :=
  stageTwoDiagramObj_interval01 C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2) h

/-- The functor sends `(0,2)` to the second component. -/
theorem stageTwoFunctor_obj_02 (S : CofiberSequenceCategory C) (h : (0 : Fin 3) ≤ 2) :
    ((stageTwoFunctor C).obj S).obj.obj (interval 0 2 h) = S.obj.obj' 1 :=
  stageTwoDiagramObj_interval02 C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2) h

/-- The functor sends `(1,2)` to the third component. -/
theorem stageTwoFunctor_obj_12 (S : CofiberSequenceCategory C) (h : (1 : Fin 3) ≤ 2) :
    ((stageTwoFunctor C).obj S).obj.obj (interval 1 2 h) = S.obj.obj' 2 :=
  stageTwoDiagramObj_interval12 C (S.obj.obj' 0) (S.obj.obj' 1) (S.obj.obj' 2) h

/-- Functoriality at `(0,1)` is the first sequence component. -/
theorem stageTwoFunctor_map_01 {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    ((stageTwoFunctor C).map φ).hom.app (interval (0 : Fin 3) 1 (by decide)) =
      ComposableArrows.app' φ.hom 0 := by
  rfl

/-- Functoriality at `(0,2)` is the second sequence component. -/
theorem stageTwoFunctor_map_02 {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    ((stageTwoFunctor C).map φ).hom.app (interval (0 : Fin 3) 2 (by decide)) =
      ComposableArrows.app' φ.hom 1 := by
  rfl

/-- Functoriality at `(1,2)` is the third sequence component. -/
theorem stageTwoFunctor_map_12 {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    ((stageTwoFunctor C).map φ).hom.app (interval (1 : Fin 3) 2 (by decide)) =
      ComposableArrows.app' φ.hom 2 := by
  rfl

/-- Functoriality at a diagonal is the identity on zero. -/
theorem stageTwoFunctor_map_diag {S T : CofiberSequenceCategory C} (φ : S ⟶ T)
    (i : Fin 3) :
    eqToHom (stageTwoFunctor_obj_diag C S i).symm ≫
        ((stageTwoFunctor C).map φ).hom.app (diag i) ≫
        eqToHom (stageTwoFunctor_obj_diag C T i) = 𝟙 (0 : C) := by
  exact (isZero_zero C).eq_of_src _ _

end CategoryTheory.Waldhausen.SConstruction
