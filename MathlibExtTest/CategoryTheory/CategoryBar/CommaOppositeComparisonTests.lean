/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryBar.CommaOppositeComparison

/-!
# Comma/opposite comparison public contract

Compile-level pins for the costructured-opposite nerve equivalence, its
simplicial promotion, and the right-comma bar versus opposite left-comma
replacement isomorphism with its load-bearing `F.op`/`op d` target, plus one
asymmetric degree-one endpoint-reversal computation on `Fin 2`.

This tests only the accepted opposite-comparison contract and makes no
naturality, contraction, homotopy, realization, or KQ claim.
-/

open CategoryTheory Opposite

universe u₁ v₁ u₂ v₂

namespace MathlibExtTest.CategoryBar.CommaOppositeComparisonTests

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

noncomputable example (F : C ⥤ D) (d : D) (n : ℕ) :
    ComposableArrows (CostructuredArrow F d) n ≃
      ComposableArrows ((StructuredArrow (op d) F.op)ᵒᵖ) n :=
  CategoryBar.costructuredOppositeNerveEquiv F d n

noncomputable example (F : C ⥤ D) (d : D) :
    nerve (CostructuredArrow F d) ≅ nerve ((StructuredArrow (op d) F.op)ᵒᵖ) :=
  CategoryBar.costructuredStructuredOppositeNerveIso F d

noncomputable example (F : C ⥤ D) (d : D) :
    CategoryBar.categoryBar (C := C) (R := CategoryBar.commaCoeffR F d)
        (L := CategoryBar.unitCoeffL C) ≅
      SimplicialObject.opFunctor.obj
        (CategoryBar.simplicialReplacement (C := Cᵒᵖ)
          (CategoryBar.commaCoeffL F.op (op d))) :=
  CategoryBar.barRightCommaOppositeLeftIso F d

/-- Identity functor on the two-object thin category `Fin 2`. -/
def finTwoF : Fin 2 ⥤ Fin 2 :=
  𝟭 _

/-- Top point for the comma coefficient, so `F.obj c ⟶ pt` is nontrivial. -/
def finTwoPt : Fin 2 :=
  1

/-- Costructured arrow over `0` with the nonidentity structure map `0 ⟶ 1`. -/
def finTwoSrc : CostructuredArrow finTwoF finTwoPt :=
  CostructuredArrow.mk (homOfLE (show (0 : Fin 2) ≤ 1 by decide))

/-- Costructured arrow over `1` with the identity structure map. -/
def finTwoTgt : CostructuredArrow finTwoF finTwoPt :=
  CostructuredArrow.mk (𝟙 finTwoPt)

/-- Nonidentity costructured-arrow morphism over `0 ⟶ 1`. -/
def finTwoHom : finTwoSrc ⟶ finTwoTgt :=
  CostructuredArrow.homMk (homOfLE (show (0 : Fin 2) ≤ 1 by decide))
    (Subsingleton.elim _ _)

example :
    (((CategoryBar.costructuredOppositeNerveEquiv finTwoF finTwoPt 1)
      (ComposableArrows.mk₁ finTwoHom)).obj ⟨0, by decide⟩).unop.right =
      op (0 : Fin 2) ∧
    (((CategoryBar.costructuredOppositeNerveEquiv finTwoF finTwoPt 1)
      (ComposableArrows.mk₁ finTwoHom)).obj ⟨1, by decide⟩).unop.right =
      op (1 : Fin 2) ∧
    (((CategoryBar.costructuredOppositeNerveEquiv finTwoF finTwoPt 1)
      (ComposableArrows.mk₁ finTwoHom)).obj ⟨0, by decide⟩).unop.hom =
      (homOfLE (show (0 : Fin 2) ≤ 1 by decide)).op :=
  ⟨rfl, rfl, rfl⟩

end MathlibExtTest.CategoryBar.CommaOppositeComparisonTests
