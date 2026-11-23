/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.ReducedNatToInt

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

namespace AlgebraicTopology

example (R : AddCommGrpCat.{0}) (n : ℕ) :
    Under.forget (TopCat.of PUnit) ⋙
        reducedSingularHomologyFunctor AddCommGrpCat.{0} R n ≅
      (singularHomologyIntTheory R).reducedH (n : ℤ) :=
  reducedSingularHomologyNatToIntIso AddCommGrpCat.{0} R n

example (R : AddCommGrpCat.{0}) (n : ℕ) (X : PointedTopCat.{0}) :
    (reducedSingularHomologyNatToIntIso AddCommGrpCat.{0} R n).app X =
      reducedSingularHomologyNatToIntObjIso AddCommGrpCat.{0} R n X := by
  rfl

example (R : AddCommGrpCat.{0}) (n : ℕ) (X : PointedTopCat.{0}) :
    (reducedSingularHomologyNatToIntIso AddCommGrpCat.{0} R n).hom.app X ≫
        (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
          (singularHomologyIntTheory R).obj (n : ℤ)).app X =
      (reducedSingularHomologyι AddCommGrpCat.{0} R n).app X.right ≫
        (singularHomologyNatToIntIso AddCommGrpCat.{0} R n).inv.app X.right := by
  exact reducedSingularHomologyNatToIntObjIso_hom_comp_reducedToPointedH
    AddCommGrpCat.{0} R n X

example {R S : AddCommGrpCat.{0}} (a : R ⟶ S) (n : ℕ)
    (X : PointedTopCat.{0}) :
    ((reducedSingularHomologyCoefficientFunctor AddCommGrpCat.{0} n).map a).app
          X.right ≫
        (reducedSingularHomologyNatToIntObjIso AddCommGrpCat.{0} S n X).hom =
      (reducedSingularHomologyNatToIntObjIso AddCommGrpCat.{0} R n X).hom ≫
        (((singularHomologyIntTheoryFunctor
          (C := AddCommGrpCat.{0}) (fun _ ↦ inferInstance)).map a).hom.homₚ
          (n : ℤ)).app (PointedTopCat.pointedPair.obj X) := by
  exact reducedSingularHomologyNatToIntIso_hom_naturality_coefficient
    AddCommGrpCat.{0} a n X

end AlgebraicTopology
