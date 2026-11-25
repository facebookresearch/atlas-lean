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

import MathlibExt.CategoryTheory.CategoryBar.CommaRightElements
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Fin.Basic

/-!
# Right-comma public contract

Compile-level pins for the right-comma coefficient `commaCoeffR`, its object and
map computations on a `Fin 2` preorder fixture with right-hom/precomposition
orientation, the covariant coefficient map `commaCoeffRMap`, and the elements
equivalence `commaElementsEquivR` with forward left-projection/hom and inverse
object computations on the asymmetric fixture.

This tests only the categorical prefix and makes no bar/nerve, naturality,
contraction, homotopy, or KQ claim.
-/

open CategoryTheory Opposite

universe u₁ v₁ u₂ v₂

namespace MathlibExtTest.CategoryBar.CommaRightElementsTests

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Identity functor on the two-object thin category `Fin 2`. -/
def finTwoF : Fin 2 ⥤ Fin 2 :=
  𝟭 _

/-- Top point for the right-comma coefficient, so `F.obj c ⟶ pt` is nontrivial. -/
def finTwoPt : Fin 2 :=
  1

noncomputable example (F : C ⥤ D) (d : D) : Cᵒᵖ ⥤ Type v₂ :=
  CategoryBar.commaCoeffR F d

example : (CategoryBar.commaCoeffR finTwoF finTwoPt).obj (op 0) =
    (finTwoF.obj 0 ⟶ finTwoPt) :=
  CategoryBar.commaCoeffR_obj finTwoF finTwoPt 0

example : (CategoryBar.commaCoeffR finTwoF finTwoPt).map
      (Quiver.Hom.op (homOfLE (show (0 : Fin 2) ≤ 1 by decide))) (𝟙 finTwoPt) =
      finTwoF.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)) ≫ (𝟙 finTwoPt) :=
  CategoryBar.commaCoeffR_map finTwoF finTwoPt _ _

noncomputable example (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    CategoryBar.commaCoeffR F d ⟶ CategoryBar.commaCoeffR F d' :=
  CategoryBar.commaCoeffRMap F g

example :
    ((CategoryBar.commaElementsEquivR finTwoF finTwoPt).functor.obj
      (op ((CategoryBar.commaCoeffR finTwoF finTwoPt).elementsMk
        (op (0 : Fin 2)) (homOfLE (show (0 : Fin 2) ≤ 1 by decide))))).left = 0 ∧
    ((CategoryBar.commaElementsEquivR finTwoF finTwoPt).functor.obj
      (op ((CategoryBar.commaCoeffR finTwoF finTwoPt).elementsMk
        (op (0 : Fin 2)) (homOfLE (show (0 : Fin 2) ≤ 1 by decide))))).hom =
      homOfLE (show (0 : Fin 2) ≤ 1 by decide) :=
  ⟨rfl, rfl⟩

example :
    ((CategoryBar.commaElementsEquivR finTwoF finTwoPt).inverse.obj
      (CostructuredArrow.mk
        (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))).unop.obj =
      op (0 : Fin 2) :=
  rfl

end MathlibExtTest.CategoryBar.CommaRightElementsTests
