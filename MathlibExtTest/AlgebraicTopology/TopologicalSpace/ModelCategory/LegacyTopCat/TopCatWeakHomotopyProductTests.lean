/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyProduct

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyIdentities

@[expose] public section

/-!
# TopCat weak-homotopy product client

Compile-time consumer checks for the KQ3 binary-product closure
`TopCat.weakHomotopyEquivalences.prodMap` in every universe. States no
arbitrary-product preservation, no `CategoryWithWeakEquivalences` instance,
no model structure, and no KQ4 `SSet` weak-equivalence claim.
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatWeakHomotopyProductTests

section BinaryProduct

theorem prodMap_client {X Y A B : TopCat.{u}} {f : X ⟶ Y} {g : A ⟶ B}
    (hf : TopCat.weakHomotopyEquivalences f)
    (hg : TopCat.weakHomotopyEquivalences g) :
    TopCat.weakHomotopyEquivalences (Limits.prod.map f g) :=
  TopCat.weakHomotopyEquivalences.prodMap hf hg

example (X A : TopCat.{u}) :
    TopCat.weakHomotopyEquivalences
      (Limits.prod.map (𝟙 X) (𝟙 A)) :=
  TopCat.weakHomotopyEquivalences.prodMap
    (TopCat.weakHomotopyEquivalences.id_mem X)
    (TopCat.weakHomotopyEquivalences.id_mem A)

section UniverseOne

example {X Y A B : TopCat.{1}} {f : X ⟶ Y} {g : A ⟶ B}
    (hf : TopCat.weakHomotopyEquivalences f)
    (hg : TopCat.weakHomotopyEquivalences g) :
    TopCat.weakHomotopyEquivalences (Limits.prod.map f g) :=
  TopCat.weakHomotopyEquivalences.prodMap hf hg

end UniverseOne

section UniverseZero

example {X Y A B : TopCat.{0}} {f : X ⟶ Y} {g : A ⟶ B}
    (hf : TopCat.weakHomotopyEquivalences f)
    (hg : TopCat.weakHomotopyEquivalences g) :
    TopCat.weakHomotopyEquivalences (Limits.prod.map f g) :=
  TopCat.weakHomotopyEquivalences.prodMap hf hg

end UniverseZero

example : True := by
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory TopCat.{u} := inferInstance
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory TopCat.{1} := inferInstance
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory TopCat.{0} := inferInstance
  trivial

#print axioms TopCat.weakHomotopyEquivalences.prodMap
#print axioms prodMap_client

end BinaryProduct

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatWeakHomotopyProductTests
