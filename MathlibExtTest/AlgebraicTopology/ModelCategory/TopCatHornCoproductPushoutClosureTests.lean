/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornCoproductPushoutProperty

@[expose] public section

/-!
# Horn-coproduct pushout closure client

Thin public client for `TopCat.coproducts_pushouts_le_weakHomotopyEquivalences`
by term application only. Forwards the property inclusion unchanged.
This is the property-level horn-pushout input only; it claims no
transfinite closure and no model structure.
-/

set_option autoImplicit false

open CategoryTheory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCoproductPushoutClosureTests

/-- Property-level horn-coproduct pushout client, by direct term application. -/
theorem coproducts_pushouts_le_weakHomotopyEquivalences_client :
    (MorphismProperty.coproducts.{0} TopCat.realizedHornInclusions.{0}).pushouts ≤
      TopCat.weakHomotopyEquivalences :=
  TopCat.coproducts_pushouts_le_weakHomotopyEquivalences

#print axioms TopCat.coproducts_pushouts_le_weakHomotopyEquivalences
#print axioms coproducts_pushouts_le_weakHomotopyEquivalences_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCoproductPushoutClosureTests
