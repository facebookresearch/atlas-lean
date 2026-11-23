/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryHomology.CoefficientCokernelHomologyAction

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology

universe uJ vJ uA

#check CategoryTheory.CategoryHomology.invertingCoefficientExtensionMap
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientExtensionMap
#check CategoryTheory.CategoryHomology.invertingCoefficientExtensionMap_app
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientExtensionMap_app
#check CategoryTheory.CategoryHomology.invertingCoefficientRootMap
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientRootMap
#check CategoryTheory.CategoryHomology.invertingCoefficientRootMap_apply
#print axioms CategoryTheory.CategoryHomology.invertingCoefficientRootMap_apply
#check CategoryTheory.CategoryHomology.coefficientCokernelFamily
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelFamily
#check CategoryTheory.CategoryHomology.coefficientCokernelFamilyX1Iso
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelFamilyX1Iso
#check CategoryTheory.CategoryHomology.coefficientCokernelFamilyX3Iso
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelFamilyX3Iso
#check CategoryTheory.CategoryHomology.coefficientCokernelFamilyIso
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelFamilyIso
#check CategoryTheory.CategoryHomology.coefficientCokernelFamily_shortExact
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelFamily_shortExact
#check CategoryTheory.CategoryHomology.coefficientCokernelHomologyProjection
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelHomologyProjection
#check CategoryTheory.CategoryHomology.coefficientCokernelHomologyBoundary
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelHomologyBoundary
#check CategoryTheory.CategoryHomology.coefficientCokernelHomologyBoundary_app
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelHomologyBoundary_app
#check CategoryTheory.CategoryHomology.coefficientCokernelHomology_exact
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelHomology_exact
#check CategoryTheory.CategoryHomology.coefficientCokernelHomologyProjection_epi_zero
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelHomologyProjection_epi_zero
#check CategoryTheory.CategoryHomology.coefficientCokernelProjectionRootMap
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelProjectionRootMap
#check CategoryTheory.CategoryHomology.coefficientCokernelProjectionRootMap_apply
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelProjectionRootMap_apply
#check CategoryTheory.CategoryHomology.coefficientCokernelBoundaryRootMap
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelBoundaryRootMap
#check CategoryTheory.CategoryHomology.coefficientCokernelBoundaryRootMap_apply
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelBoundaryRootMap_apply
#check CategoryTheory.CategoryHomology.coefficientCokernelRootMaps_exact
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelRootMaps_exact
#check CategoryTheory.CategoryHomology.coefficientCokernelProjectionRootMap_zero_surjective
#print axioms CategoryTheory.CategoryHomology.coefficientCokernelProjectionRootMap_zero_surjective

namespace CoefficientCokernelHomologyActionTests

variable {J : Type uJ} [Category.{vJ} J]

section Natural

variable {M N : J ⥤ AddCommGrpCat.{uA}}
  [∀ {i j : J} (f : i ⟶ j), IsIso (M.map f)]
  [∀ {i j : J} (f : i ⟶ j), IsIso (N.map f)]
  (α : M ⟶ N) (i : J)

example (g : End ((SSet.categoryNerveUnit J).obj i)) (v : M.obj i) :
    (α.app i).hom (invertingCoefficientRootAction M i g v) =
      invertingCoefficientRootAction N i g ((α.app i).hom v) := by
  have hNat := Representation.IntertwiningMap.isIntertwining
    (invertingCoefficientRootAction M i) (invertingCoefficientRootAction N i)
    (invertingCoefficientRootMap M α i) g v
  have hSource := invertingCoefficientRootMap_apply M α i
    (invertingCoefficientRootAction M i g v)
  have hTarget := invertingCoefficientRootMap_apply M α i v
  exact hSource.symm.trans
    (hNat.trans (congrArg (invertingCoefficientRootAction N i g) hTarget))

example (v : M.obj i) : invertingCoefficientRootMap M α i v = (α.app i).hom v :=
  invertingCoefficientRootMap_apply M α i v

end Natural

variable {A B : J ⥤ ChainComplex AddCommGrpCat.{uA} ℕ} (α : A ⟶ B) [Mono α]

example (n : ℕ) (i : J) :
    (coefficientCokernelHomologyBoundary α n).app i =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) (n + 1)).map
          (coefficientCokernelFamilyX3Iso α i).inv ≫
        (coefficientCokernelFamily_shortExact α i).δ (n + 1) n
          (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{uA} (ComplexShape.down ℕ) n).map
          (coefficientCokernelFamilyX1Iso α i).hom :=
  coefficientCokernelHomologyBoundary_app α n i

example (n : ℕ) (i : J) : Function.Exact
    ((coefficientCokernelHomologyProjection α (n + 1)).app i)
    ((coefficientCokernelHomologyBoundary α n).app i) :=
  coefficientCokernelHomology_exact α n i

example (i : J) : Epi ((coefficientCokernelHomologyProjection α 0).app i) :=
  coefficientCokernelHomologyProjection_epi_zero α i

section Root

variable (n : ℕ)
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((B ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) (n + 1)).map f)]
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((cokernel α ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) (n + 1)).map f)]
  [∀ {i j : J} (f : i ⟶ j), IsIso
    ((A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
      (ComplexShape.down ℕ) n).map f)]

example (i : J) : Function.Exact (coefficientCokernelProjectionRootMap α (n + 1) i)
    (coefficientCokernelBoundaryRootMap α n i) :=
  coefficientCokernelRootMaps_exact α n i

end Root

example
    [∀ {i j : J} (f : i ⟶ j), IsIso
      ((B ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
        (ComplexShape.down ℕ) 0).map f)]
    [∀ {i j : J} (f : i ⟶ j), IsIso
      ((cokernel α ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{uA}
        (ComplexShape.down ℕ) 0).map f)]
    (i : J) : Function.Surjective (coefficientCokernelProjectionRootMap α 0 i) :=
  coefficientCokernelProjectionRootMap_zero_surjective α i

end CoefficientCokernelHomologyActionTests
