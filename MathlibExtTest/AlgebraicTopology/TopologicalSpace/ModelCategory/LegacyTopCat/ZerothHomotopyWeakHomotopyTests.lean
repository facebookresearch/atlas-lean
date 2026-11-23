/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.ZerothHomotopyWeakHomotopy

/-!
# Tests for zeroth homotopy and weak homotopy equivalences
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe u

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
namespace ZerothHomotopyWeakHomotopyTests

section TopCatBridge

variable {A B : TopCat.{u}} {h : A ⟶ B}

example (hh : TopCat.weakHomotopyEquivalences h) :
    Function.Bijective (TopCat.zerothHomotopyMap h) :=
  hh.bijective_zerothHomotopyMap

end TopCatBridge

#print axioms
  TopCat.weakHomotopyEquivalences.bijective_zerothHomotopyMap

end ZerothHomotopyWeakHomotopyTests
end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
