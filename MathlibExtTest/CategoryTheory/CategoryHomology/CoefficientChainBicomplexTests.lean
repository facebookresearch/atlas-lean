/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryHomology.CoefficientChainBicomplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology
open scoped Simplicial

universe uG vG uA vA uB vB w

#check nervePullbackCoefficientDegreeChangeOfCategoryIso
#print axioms nervePullbackCoefficientDegreeChangeOfCategoryIso
#check nervePullbackCoefficientDegreeChangeOfCategoryIso_ι
#print axioms nervePullbackCoefficientDegreeChangeOfCategoryIso_ι
#check nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι
#print axioms nervePullbackCoefficientDegreeChangeOfCategoryIso_inv_ι
#check nervePullbackCoefficientSimplicialChangeOfCategoryIso
#print axioms nervePullbackCoefficientSimplicialChangeOfCategoryIso
#check nervePullbackCoefficientComplexChangeOfCategoryIso
#print axioms nervePullbackCoefficientComplexChangeOfCategoryIso
#check nervePullbackCoefficientComplexChangeOfCategoryIso_hom_f
#print axioms nervePullbackCoefficientComplexChangeOfCategoryIso_hom_f
#check nervePullbackCoefficientComplexChangeOfCategoryIso_base
#print axioms nervePullbackCoefficientComplexChangeOfCategoryIso_base
#check coefficientBarComplexChangeOfCategoryIso
#print axioms coefficientBarComplexChangeOfCategoryIso
#check coefficientChainVerticalHomologyIso
#print axioms coefficientChainVerticalHomologyIso
#check coefficientChainSecondPageIso
#print axioms coefficientChainSecondPageIso

namespace CoefficientChainBicomplexTests

example {G : Type uG} [Category.{vG} G]
    {A : Type uA} [Category.{vA} A] [HasCoproducts.{max uG vG} A]
    {B : Type uB} [Category.{vB} B] [HasCoproducts.{max uG vG} B]
    (F : A ⥤ B) [PreservesColimitsOfSize.{max uG vG, max uG vG} F]
    {X : SSet.{max uG vG}} (f : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)
    (n : ℕ) (x : X _⦋n⦌) :
    F.map (nervePullbackCoefficientι f M x) ≫
        (nervePullbackCoefficientDegreeChangeOfCategoryIso F f M n).hom =
      nervePullbackCoefficientι f (M ⋙ F) x :=
  nervePullbackCoefficientDegreeChangeOfCategoryIso_ι F f M n x

noncomputable example {J : Type w} [Category.{0} J]
    (D : J ⥤ ChainComplex AddCommGrpCat.{w} ℕ) (q : ℕ) :
    (coefficientChainBicomplex D).verticalHomologyComplex q ≅
      coefficientBarComplex
        (D ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ) q) :=
  coefficientChainVerticalHomologyIso D q

noncomputable example {J : Type w} [Category.{0} J]
    (A B : J ⥤ ChainComplex AddCommGrpCat.{w} ℕ) (i : A ⟶ B) (p q : ℕ) :
    ((coefficientChainSpectralSequence (cokernel i)).page 2).X (p, q) ≅
      homologyWithCoefficients
        (cokernel i ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ) q) p :=
  coefficientChainSecondPageIso (cokernel i) p q

end CoefficientChainBicomplexTests
