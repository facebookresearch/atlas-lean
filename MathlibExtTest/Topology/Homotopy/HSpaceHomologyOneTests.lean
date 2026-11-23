/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.HSpaceHomologyOne

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open TopCat.HSpaceHomologyOne

universe u

namespace HSpaceHomologyOneTests

#check abelianizationMap_bijective_of_integralHomologyOne_isIso
#print axioms abelianizationMap_bijective_of_integralHomologyOne_isIso
#check fundamentalGroupMap_bijective_of_integralHomologyOne_isIso
#print axioms fundamentalGroupMap_bijective_of_integralHomologyOne_isIso

example {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) (x : X) :
    Function.Bijective (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x)) :=
  fundamentalGroupMap_bijective_of_integralHomologyOne_isIso f hf x

example {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f)) :
    ∀ x : X, Function.Bijective (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x)) :=
  fun x => fundamentalGroupMap_bijective_of_integralHomologyOne_isIso f (hf 1) x

end HSpaceHomologyOneTests
