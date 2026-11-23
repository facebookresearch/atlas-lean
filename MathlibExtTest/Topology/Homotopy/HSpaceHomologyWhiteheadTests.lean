/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.HSpaceHomologyWhitehead

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomotopicalAlgebra
open scoped TopCat.modelCategory ContinuousMap

universe u v w

#check TopCat.HSpaceHomologyWhitehead.originalRegularCover_integralHomology_isIso
#print axioms TopCat.HSpaceHomologyWhitehead.originalRegularCover_integralHomology_isIso
#check TopCat.HSpaceHomologyWhitehead.allLocalCoefficientHomologyEquivalence_of_integralHomology_isIso
#print axioms TopCat.HSpaceHomologyWhitehead.allLocalCoefficientHomologyEquivalence_of_integralHomology_isIso
#check TopCat.HSpaceHomologyWhitehead.mem_weakHomotopyEquivalences_of_integralHomology_isIso
#print axioms TopCat.HSpaceHomologyWhitehead.mem_weakHomotopyEquivalences_of_integralHomology_isIso
#check TopCat.HSpaceHomologyWhitehead.homotopyEquiv_of_integralHomology_isIso
#print axioms TopCat.HSpaceHomologyWhitehead.homotopyEquiv_of_integralHomology_isIso
#check TopCat.HSpaceHomologyWhitehead.exists_actual_inverse_of_integralHomology_isIso
#print axioms TopCat.HSpaceHomologyWhitehead.exists_actual_inverse_of_integralHomology_isIso
#check TopCat.HSpaceHomologyWhitehead.exists_point_relative_inverse_of_integralHomology_isIso
#print axioms TopCat.HSpaceHomologyWhitehead.exists_point_relative_inverse_of_integralHomology_isIso

namespace HSpaceHomologyWhiteheadTests

open TopCat.HSpaceHomologyWhitehead

example {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((singularIntegralHomologyFunctor n).map f)) :
    TopCat.weakHomotopyEquivalences f :=
  mem_weakHomotopyEquivalences_of_integralHomology_isIso f hf

variable {X Y : TopCat.{u}} [HSpace X] [HSpace Y] [ConnectedSpace X] [ConnectedSpace Y]
  (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
    ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
  (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
    ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
  (f : X ⟶ Y) (hf : ∀ n : ℕ, IsIso ((singularIntegralHomologyFunctor n).map f))

example : ∃ e : X ≃ₕ Y, e.toFun = f.hom :=
  homotopyEquiv_of_integralHomology_isIso hCWX hCWY f hf

example : ∃ g : Y ⟶ X, Nonempty (TopCat.Homotopy (f ≫ g) (𝟙 X)) ∧
    Nonempty (TopCat.Homotopy (g ≫ f) (𝟙 Y)) :=
  exists_actual_inverse_of_integralHomology_isIso hCWX hCWY f hf

example (x : X)
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [Cofibration (TopCat.const (f x) : TopCat.of PUnit.{u + 1} ⟶ Y)] :
    ∃ g : Y ⟶ X, g (f x) = x ∧
      Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 X : X ⟶ X).hom {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom {f x}) :=
  exists_point_relative_inverse_of_integralHomology_isIso hCWX hCWY f hf x

end HSpaceHomologyWhiteheadTests
