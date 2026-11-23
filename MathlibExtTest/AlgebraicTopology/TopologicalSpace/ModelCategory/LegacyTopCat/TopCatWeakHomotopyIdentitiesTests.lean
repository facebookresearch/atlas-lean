/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyIdentities

@[expose] public section

/-!
# TopCat weak-homotopy identities client

Compile-time consumer checks for the KQ3 `TopCat.weakHomotopyEquivalences`
ContainsIdentities packaging: the inherited instance plus direct identity
membership for `TopCat.{0}`. States no `CategoryWithWeakEquivalences`
instance, no model structure, no product closure, and no KQ4 `SSet`
weak-equivalence claim.
-/

set_option autoImplicit false

open CategoryTheory MorphismProperty

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatWeakHomotopyIdentitiesTests

section ContainsIdentities

theorem containsIdentities_client :
    TopCat.weakHomotopyEquivalences.ContainsIdentities :=
  inferInstance

#print axioms TopCat.weakHomotopyEquivalences
#print axioms containsIdentities_client

end ContainsIdentities

section IdentityMembership

theorem id_mem_client (X : TopCat.{0}) :
    TopCat.weakHomotopyEquivalences (𝟙 X) :=
  id_mem TopCat.weakHomotopyEquivalences X

#print axioms id_mem_client

end IdentityMembership

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatWeakHomotopyIdentitiesTests
