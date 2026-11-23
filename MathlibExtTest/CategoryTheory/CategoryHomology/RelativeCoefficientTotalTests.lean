/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryHomology.RelativeCoefficientTotal

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology

universe w

local instance : HasCoproducts.{w} (ChainComplex AddCommGrpCat.{w} ℕ) := fun I =>
  let : Small.{w} (Discrete I) := small_self (Discrete I)
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  HomologicalComplex.instHasColimitsOfShape

#check alternatingCoefficientBarFunctor
#print axioms alternatingCoefficientBarFunctor
#check coefficientBarCokernelIso
#print axioms coefficientBarCokernelIso
#check coefficientBarCokernelIso_projection
#print axioms coefficientBarCokernelIso_projection
#check coefficientChainTotalFunctor
#print axioms coefficientChainTotalFunctor
#check coefficientRelativeTotalIso
#print axioms coefficientRelativeTotalIso
#check coefficientRelativeTotalIso_projection
#print axioms coefficientRelativeTotalIso_projection

namespace RelativeCoefficientTotalTests

variable {J : Type w} [Category.{0} J]
  {D E : J ⥤ ChainComplex AddCommGrpCat.{w} ℕ} (α : D ⟶ E)

noncomputable example : coefficientBarComplex (cokernel α) ≅
    cokernel ((alternatingCoefficientBarFunctor (J := J)
      (A := ChainComplex AddCommGrpCat.{w} ℕ)).map α) :=
  coefficientBarCokernelIso α

example :
    (alternatingCoefficientBarFunctor (J := J)
        (A := ChainComplex AddCommGrpCat.{w} ℕ)).map (cokernel.π α) ≫
      (coefficientBarCokernelIso α).hom =
    cokernel.π ((alternatingCoefficientBarFunctor (J := J)
      (A := ChainComplex AddCommGrpCat.{w} ℕ)).map α) :=
  coefficientBarCokernelIso_projection α

example :
    (coefficientChainTotalFunctor (J := J)).map (cokernel.π α) ≫
      (coefficientRelativeTotalIso α).hom =
    cokernel.π ((coefficientChainTotalFunctor (J := J)).map α) :=
  coefficientRelativeTotalIso_projection α

end RelativeCoefficientTotalTests
