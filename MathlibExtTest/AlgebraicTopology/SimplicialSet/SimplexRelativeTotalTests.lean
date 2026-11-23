/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexRelativeTotal

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology

universe w

#check SSet.simplexTotalAugmentation
#print axioms SSet.simplexTotalAugmentation
#check SSet.simplexTotalAugmentation_quasiIso
#print axioms SSet.simplexTotalAugmentation_quasiIso
#check SSet.simplexTotalAugmentation_naturality
#print axioms SSet.simplexTotalAugmentation_naturality
#check SSet.simplexRelativeTotalAugmentation
#print axioms SSet.simplexRelativeTotalAugmentation
#check SSet.simplexRelativeTotalAugmentation_projection
#print axioms SSet.simplexRelativeTotalAugmentation_projection
#check SSet.simplexRelativeTotalAugmentation_quasiIso
#print axioms SSet.simplexRelativeTotalAugmentation_quasiIso
#check SSet.simplexRelativeCoefficientTotal_acyclic_of_homology_isIso
#print axioms SSet.simplexRelativeCoefficientTotal_acyclic_of_homology_isIso

namespace SimplexRelativeTotalTests

variable (R : AddCommGrpCat.{w}) {Z Z' B : SSet.{w}}
  {p : Z ⟶ B} {q : Z' ⟶ B} (u : Z ⟶ Z') (hu : u ≫ q = p)

example :
    (SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map
        (SSet.simplexPullbackDiagramMap u hu) ≫ SSet.simplexTotalAugmentation R q =
      SSet.simplexTotalAugmentation R p ≫ SSet.chainComplexMap u R :=
  SSet.simplexTotalAugmentation_naturality R u hu

example [Mono u] : QuasiIso (SSet.simplexRelativeTotalAugmentation R u hu) :=
  SSet.simplexRelativeTotalAugmentation_quasiIso R u hu

example [Mono u] (h : ∀ n : ℕ, IsIso (SSet.homologyMap u R n)) :
    (SSet.simplexRelativeCoefficientTotal R u hu).Acyclic :=
  SSet.simplexRelativeCoefficientTotal_acyclic_of_homology_isIso R u hu h

end SimplexRelativeTotalTests
