/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryBar.CommaRightComparison
import MathlibExt.CategoryTheory.NerveData
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Right-comma degreewise equivalence public contract

Compile-level pins for `barRightCommaEquiv`: its exact general type, the
forward left-projection computation, the inverse endpoint formula, and one
degree-one forward left-projection check on a
`Fin 2` preorder fixture, plus the four simplicial compatibility pins
`barRightComma_face_zero`, `barRightComma_face_interior`,
`barRightComma_face_last`, and `barRightComma_degeneracy`, the full
Data-level natural-transformation equations `barRightComma_face_compat` and
`barRightComma_degeneracy_compat`, and the Data/simplicial packaging
`barRightCommaDataIso` and `barRightCommaSimplicialIso`.

This tests only the accepted degreewise, face/degeneracy compatibility, and
Data/simplicial packaging contract and makes no naturality, contraction,
homotopy, realization, or KQ claim.
-/

open CategoryTheory Opposite

universe u₁ v₁ u₂ v₂

namespace MathlibExtTest.CategoryBar.CommaRightComparisonTests

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Identity functor on the two-object thin category `Fin 2`. -/
def finTwoF : Fin 2 ⥤ Fin 2 :=
  𝟭 _

/-- Top point for the right-comma coefficient, so `F.obj c ⟶ pt` is nontrivial. -/
def finTwoPt : Fin 2 :=
  1

noncomputable example (F : C ⥤ D) (d : D) (n : ℕ) :
    CategoryBar.barObj C (CategoryBar.commaCoeffR F d)
        (CategoryBar.unitCoeffL C) n ≃
      ComposableArrows (CostructuredArrow F d) n :=
  CategoryBar.barRightCommaEquiv F d n

example (F : C ⥤ D) (d : D) (n : ℕ)
    (x : CategoryBar.barObj C (CategoryBar.commaCoeffR F d)
      (CategoryBar.unitCoeffL C) n) (i : Fin (n + 1)) :
    (((CategoryBar.barRightCommaEquiv F d n) x).obj i).left =
      (CategoryBar.barChain x).obj i :=
  CategoryBar.barRightCommaEquiv_apply_left F d n x i

example (F : C ⥤ D) (d : D) (n : ℕ)
    (Y : ComposableArrows (CostructuredArrow F d) n) :
    (CategoryBar.barRightCommaEquiv F d n).symm Y =
      ⟨Y ⋙ CostructuredArrow.proj F d, ULift.up PUnit.unit,
        CostructuredArrow.hom (Y.obj (Fin.last n))⟩ :=
  CategoryBar.barRightCommaEquiv_symm_apply F d n Y

example :
    ((CategoryBar.barRightCommaEquiv finTwoF finTwoPt 1
      ⟨ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 by decide)),
        ULift.up PUnit.unit, 𝟙 finTwoPt⟩).obj ⟨0, by decide⟩).left = 0 ∧
    ((CategoryBar.barRightCommaEquiv finTwoF finTwoPt 1
      ⟨ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 by decide)),
        ULift.up PUnit.unit, 𝟙 finTwoPt⟩).obj ⟨1, by decide⟩).left = 1 :=
  ⟨rfl, rfl⟩

example {n : ℕ} (F : C ⥤ D) (d : D)
    (x : CategoryBar.barObj C (CategoryBar.commaCoeffR F d)
      (CategoryBar.unitCoeffL C) (n + 1)) :
    (nerve (CostructuredArrow F d)).δ (0 : Fin (n + 2))
        (CategoryBar.barRightCommaEquiv F d (n + 1) x) =
      CategoryBar.barRightCommaEquiv F d n
        (CategoryBar.barδ (0 : Fin (n + 2)) x) :=
  CategoryBar.barRightComma_face_zero F d x

example {n : ℕ} (q : Fin n) (F : C ⥤ D) (d : D)
    (x : CategoryBar.barObj C (CategoryBar.commaCoeffR F d)
      (CategoryBar.unitCoeffL C) (n + 1)) :
    (nerve (CostructuredArrow F d)).δ q.castSucc.succ
        (CategoryBar.barRightCommaEquiv F d (n + 1) x) =
      CategoryBar.barRightCommaEquiv F d n
        (CategoryBar.barδ q.castSucc.succ x) :=
  CategoryBar.barRightComma_face_interior q F d x

example {n : ℕ} (i : Fin (n + 1)) (F : C ⥤ D) (d : D)
    (x : CategoryBar.barObj C (CategoryBar.commaCoeffR F d)
      (CategoryBar.unitCoeffL C) n) :
    (nerve (CostructuredArrow F d)).σ i
        (CategoryBar.barRightCommaEquiv F d n x) =
      CategoryBar.barRightCommaEquiv F d (n + 1)
        (CategoryBar.barσ i x) :=
  CategoryBar.barRightComma_degeneracy i F d x

example {n : ℕ} (F : C ⥤ D) (d : D)
    (x : CategoryBar.barObj C (CategoryBar.commaCoeffR F d)
      (CategoryBar.unitCoeffL C) (n + 1)) :
    (nerve (CostructuredArrow F d)).δ (Fin.last (n + 1))
        (CategoryBar.barRightCommaEquiv F d (n + 1) x) =
      CategoryBar.barRightCommaEquiv F d n
        (CategoryBar.barδ (Fin.last (n + 1)) x) :=
  CategoryBar.barRightComma_face_last F d x

example {n : ℕ} (i : Fin (n + 2)) (F : C ⥤ D) (d : D) :
    (Equiv.toIso (CategoryBar.barRightCommaEquiv F d (n + 1))).hom ≫
        (CategoryTheory.nerveData (CostructuredArrow F d)).δ i =
      (CategoryBar.categoryBarData (R := CategoryBar.commaCoeffR F d)
        (L := CategoryBar.unitCoeffL C)).δ i ≫
        (Equiv.toIso (CategoryBar.barRightCommaEquiv F d n)).hom :=
  CategoryBar.barRightComma_face_compat i F d

example {n : ℕ} (i : Fin (n + 1)) (F : C ⥤ D) (d : D) :
    (Equiv.toIso (CategoryBar.barRightCommaEquiv F d n)).hom ≫
        (CategoryTheory.nerveData (CostructuredArrow F d)).σ i =
      (CategoryBar.categoryBarData (R := CategoryBar.commaCoeffR F d)
        (L := CategoryBar.unitCoeffL C)).σ i ≫
        (Equiv.toIso (CategoryBar.barRightCommaEquiv F d (n + 1))).hom :=
  CategoryBar.barRightComma_degeneracy_compat i F d

noncomputable example (F : C ⥤ D) (d : D) :
    CategoryBar.categoryBarData (R := CategoryBar.commaCoeffR F d)
        (L := CategoryBar.unitCoeffL C) ≅
      CategoryTheory.nerveData (CostructuredArrow F d) :=
  CategoryBar.barRightCommaDataIso F d

noncomputable example (F : C ⥤ D) (d : D) :
    CategoryBar.categoryBar (R := CategoryBar.commaCoeffR F d)
        (L := CategoryBar.unitCoeffL C) ≅
      nerve (CostructuredArrow F d) :=
  CategoryBar.barRightCommaSimplicialIso F d

end MathlibExtTest.CategoryBar.CommaRightComparisonTests
