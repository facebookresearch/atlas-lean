/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.NerveData
import MathlibExt.CategoryTheory.CategoryBar.RightUnitBridge
import MathlibExt.CategoryTheory.CategoryBar.NerveNaturality

/-!
# Category bar unit-coefficient nerve comparison public contract

Compile-level pins for the unit coefficients, the degreewise equivalence
with the nerve, its `Data`/`SSet` promotions, face and degeneracy compatibility,
the unit-elements bridge, the right-unit bridge, the comparison triangle,
and functor naturality of the unit-bar nerve comparison.
-/

open CategoryTheory Opposite

universe u v

namespace MathlibExtTest.CategoryBar.NerveComparisonTests

variable {C : Type u} [Category.{v} C]

example : C ⥤ Type 0 :=
  CategoryBar.unitCoeffL C

example : Cᵒᵖ ⥤ Type 0 :=
  CategoryBar.unitCoeffR C

example (n : ℕ)
    (x : CategoryBar.barObj C (CategoryBar.unitCoeffR C)
      (CategoryBar.unitCoeffL C) n) :
    CategoryBar.barNerveUnitEquiv C n x = CategoryBar.barChain x :=
  CategoryBar.barNerveUnitEquiv_apply n x

example (n : ℕ) (F : ComposableArrows C n) :
    (CategoryBar.barNerveUnitEquiv C n).symm F =
        ⟨F, ULift.up PUnit.unit, ULift.up PUnit.unit⟩ :=
  CategoryBar.barNerveUnitEquiv_symm_apply n F

noncomputable example :
    CategoryBar.categoryBarData (C := C) (R := CategoryBar.unitCoeffR C)
        (L := CategoryBar.unitCoeffL C) ≅ CategoryTheory.nerveData C :=
  CategoryBar.barNerveUnitDataIso C

noncomputable example :
    CategoryBar.categoryBar (C := C) (R := CategoryBar.unitCoeffR C)
        (L := CategoryBar.unitCoeffL C) ≅ nerve C :=
  CategoryBar.barNerveUnitSimplicialIso C

example {n : ℕ} (i : Fin (n + 2)) :
    (Equiv.toIso (CategoryBar.barNerveUnitEquiv C (n + 1))).hom ≫
        (CategoryTheory.nerveData C).δ i =
      (CategoryBar.categoryBarData (C := C) (R := CategoryBar.unitCoeffR C)
        (L := CategoryBar.unitCoeffL C)).δ i ≫
        (Equiv.toIso (CategoryBar.barNerveUnitEquiv C n)).hom :=
  CategoryBar.barNerveUnit_face_compat i

example {n : ℕ} (i : Fin (n + 1)) :
    (Equiv.toIso (CategoryBar.barNerveUnitEquiv C n)).hom ≫
        (CategoryTheory.nerveData C).σ i =
      (CategoryBar.categoryBarData (C := C) (R := CategoryBar.unitCoeffR C)
        (L := CategoryBar.unitCoeffL C)).σ i ≫
        (Equiv.toIso (CategoryBar.barNerveUnitEquiv C (n + 1))).hom :=
  CategoryBar.barNerveUnit_degeneracy_compat i

noncomputable example : C ⥤ (CategoryBar.unitCoeffL C).Elements :=
  CategoryBar.unitElementsSection C

noncomputable example : (CategoryBar.unitCoeffL C).Elements ≌ C :=
  CategoryBar.unitElementsEquiv C

noncomputable example (n : ℕ) :
    ComposableArrows (CategoryBar.unitCoeffL C).Elements n ≃
      ComposableArrows C n :=
  CategoryBar.unitElementsNerveEquiv C n

noncomputable example :
    ∃ _I : nerve (CategoryBar.unitCoeffL C).Elements ≅ nerve C,
      _I.hom = nerveMap (Functor.Elements.π (CategoryBar.unitCoeffL C)) :=
  ⟨CategoryBar.unitElementsNerveIso C, CategoryBar.unitElementsNerveIso_hom C⟩

noncomputable example : CategoryBar.replUnit C ≅ CategoryBar.unitCoeffR C :=
  CategoryBar.replUnitIsoUnitCoeffR C

noncomputable example :
    CategoryBar.simplicialReplacementData (CategoryBar.unitCoeffL C) ≅
      CategoryBar.categoryBarData (R := CategoryBar.unitCoeffR C)
        (L := CategoryBar.unitCoeffL C) :=
  CategoryBar.replUnitBarDataIso C

noncomputable example :
    CategoryBar.simplicialReplacement (CategoryBar.unitCoeffL C) ≅
      CategoryBar.categoryBar (R := CategoryBar.unitCoeffR C)
        (L := CategoryBar.unitCoeffL C) :=
  CategoryBar.replUnitBarSimplicialIso C

example :
    (CategoryBar.replUnitBarSimplicialIso C).hom ≫
        (CategoryBar.barNerveUnitSimplicialIso C).hom =
      (CategoryBar.replNerveSimplicialIso (CategoryBar.unitCoeffL C)).hom ≫
        (CategoryBar.unitElementsNerveIso C).hom :=
  CategoryBar.replUnit_comparison_triangle C

example {D : Type u} [Category.{v} D] (F : C ⥤ D) :
    CategoryBar.unitCoeffL C ⟶ F ⋙ CategoryBar.unitCoeffL D :=
  CategoryBar.unitIdxL F

example {D : Type u} [Category.{v} D] (F : C ⥤ D) :
    CategoryBar.unitCoeffR C ⟶ F.op ⋙ CategoryBar.unitCoeffR D :=
  CategoryBar.unitIdxR F

example {D : Type u} [Category.{v} D] (F : C ⥤ D) {n : ℕ}
    (x : CategoryBar.barObj C (CategoryBar.unitCoeffR C)
      (CategoryBar.unitCoeffL C) n) :
    CategoryBar.barNerveUnitEquiv D n (CategoryBar.barIdxMap F
        (CategoryBar.unitIdxR F) (CategoryBar.unitIdxL F) x) =
      (nerveMap F).app (Opposite.op (SimplexCategory.mk n))
        (CategoryBar.barNerveUnitEquiv C n x) :=
  CategoryBar.barNerveUnit_indexNaturality F x

example {D : Type u} [Category.{v} D] (F : C ⥤ D) :
    CategoryBar.categoryBarIdxMap F (CategoryBar.unitIdxR F)
        (CategoryBar.unitIdxL F) ≫
        (CategoryBar.barNerveUnitSimplicialIso D).hom =
      (CategoryBar.barNerveUnitSimplicialIso C).hom ≫ nerveMap F :=
  CategoryBar.barNerveUnitSimplicial_indexNaturality F

end MathlibExtTest.CategoryBar.NerveComparisonTests
