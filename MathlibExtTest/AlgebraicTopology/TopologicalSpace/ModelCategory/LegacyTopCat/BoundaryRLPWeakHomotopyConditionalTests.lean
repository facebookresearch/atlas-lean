/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.BoundaryRLPWeakHomotopyConditional

@[expose] public section

/-!
# Conditional boundary-RLP weak-equivalence bridge client

Thin public client for
`TopCat.boundaryRLP_le_weakHomotopyEquivalences_of_kanRestricted_Irlp_le_W`
by term application only. Accepts the same explicit Kan-restricted
higher-order hypothesis
`∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f` and invokes
the provider's conditional inclusion. The unrestricted `I.rlp ≤ W` is false:
identities on non-Kan simplicial sets are in `I.rlp` but not `W`. Supplies
no premise, adds no instance, and claims no unconditional weak equivalence
or model structure.
-/

set_option autoImplicit false

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.BoundaryRLPWeakHomotopyConditionalTests

/-- Conditional bridge client: the explicit Kan-restricted boundary-RLP hypothesis
implies realized boundary-RLP maps are weak homotopy equivalences. -/
theorem le_client
    (h : ∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f) :
    TopCat.realizedBoundaryInclusions.{u}.rlp ≤ TopCat.weakHomotopyEquivalences :=
  TopCat.boundaryRLP_le_weakHomotopyEquivalences_of_kanRestricted_Irlp_le_W h

example
    (h : ∀ {X Y : SSet.{1}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{1}.rlp f → SSet.KanComplex.W.{1} f) :
    TopCat.realizedBoundaryInclusions.{1}.rlp ≤ TopCat.weakHomotopyEquivalences :=
  le_client h

example
    (h : ∀ {X Y : SSet.{0}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{0}.rlp f → SSet.KanComplex.W.{0} f) :
    TopCat.realizedBoundaryInclusions.{0}.rlp ≤ TopCat.weakHomotopyEquivalences :=
  le_client h

#print axioms TopCat.boundaryRLP_le_weakHomotopyEquivalences_of_kanRestricted_Irlp_le_W
#print axioms le_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.BoundaryRLPWeakHomotopyConditionalTests
