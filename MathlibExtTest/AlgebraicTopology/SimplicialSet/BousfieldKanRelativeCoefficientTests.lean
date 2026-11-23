/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanRelativeCoefficient

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology
open scoped Simplicial

universe w

local instance : HasCoproducts.{w} (ChainComplex AddCommGrpCat.{w} ℕ) := fun I =>
  let : Small.{w} (Discrete I) := small_self (Discrete I)
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  HomologicalComplex.instHasColimitsOfShape

#check SSet.bkCoefficientChainIso
#print axioms SSet.bkCoefficientChainIso
#check SSet.bkCoefficientChainIso_summand
#print axioms SSet.bkCoefficientChainIso_summand
#check SSet.bkCoefficientChainIso_naturality
#print axioms SSet.bkCoefficientChainIso_naturality
#check SSet.bkCoefficientChainTotalIso
#print axioms SSet.bkCoefficientChainTotalIso
#check SSet.bkCoefficientChainTotalIso_naturality
#print axioms SSet.bkCoefficientChainTotalIso_naturality
#check SSet.bkRelativeCoefficientTotalIso
#print axioms SSet.bkRelativeCoefficientTotalIso
#check SSet.bkRelativeCoefficientTotalIso_projection
#print axioms SSet.bkRelativeCoefficientTotalIso_projection

namespace BousfieldKanRelativeCoefficientTests

variable {J : Type w} [Category.{0} J]
  (R : AddCommGrpCat.{w}) {D E : J ⥤ SSet.{w}} (α : D ⟶ E)

example (p : ℕ) (s : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) p) :
    SSet.chainComplexMap
        (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s) R ≫
      (SSet.bkCoefficientChainIso R D).hom.f p =
    coefficientBarι (D ⋙ (SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R) s.1 :=
  SSet.bkCoefficientChainIso_summand R D p s

example :
    (SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α ≫
        (SSet.bkCoefficientChainTotalIso R E).hom =
      (SSet.bkCoefficientChainTotalIso R D).hom ≫
        (coefficientChainTotalFunctor (J := J)).map
          (Functor.whiskerRight α ((SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R)) :=
  SSet.bkCoefficientChainTotalIso_naturality R α

noncomputable example :
    cokernel ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α) ≅
      (coefficientChainTotalFunctor (J := J)).obj
        (cokernel
          (Functor.whiskerRight α ((SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R))) :=
  SSet.bkRelativeCoefficientTotalIso R α

example :
    cokernel.π ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α) ≫
        (SSet.bkRelativeCoefficientTotalIso R α).hom =
      (SSet.bkCoefficientChainTotalIso R E).hom ≫
        (coefficientChainTotalFunctor (J := J)).map
          (cokernel.π
            (Functor.whiskerRight α ((SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R))) :=
  SSet.bkRelativeCoefficientTotalIso_projection R α

end BousfieldKanRelativeCoefficientTests
