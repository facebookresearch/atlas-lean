/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyCategory

@[expose] public section

/-!
# TopCat weak-homotopy category client

Compile-time consumer checks for the KQ3 `TopCat` universe-zero
`CategoryWithWeakEquivalences` packaging: the instance itself plus direct
identity weak equivalences for `TopCat.{0}`. States no model structure, no
factorization system, no product closure, and no KQ4 `SSet` weak-equivalence
claim.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatWeakHomotopyCategoryTests

section CategoryInstance

abbrev category_client : CategoryWithWeakEquivalences TopCat.{0} :=
  inferInstance

#print axioms TopCat.weakHomotopyEquivalences
#print axioms category_client

end CategoryInstance

section IdentityWeakEquivalences

theorem id_weakEquivalence_client (X : TopCat.{0}) :
    weakEquivalences TopCat.{0} (𝟙 X) :=
  id_mem (weakEquivalences TopCat.{0}) X

#print axioms id_weakEquivalence_client

end IdentityWeakEquivalences

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatWeakHomotopyCategoryTests
