/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatTrivialFibrationRecognition

@[expose] public section

/-!
# Conditional trivial-fibration recognition client

Thin public client for `TopCat.hornRLP_inf_W_le_boundaryRLP_of_sSet` by term
application only. Accepts the same explicit simplicial-set hypothesis
`SSet.modelCategoryQuillen.J.rlp ⊓ SSet.KanComplex.W ≤
SSet.modelCategoryQuillen.I.rlp` and invokes the provider's conditional
inclusion. Supplies no premise, adds no instance, and claims no reverse
inclusion, no equality, and no model structure.
-/

set_option autoImplicit false

universe u

namespace MathlibExtTest
namespace AlgebraicTopology
namespace ModelCategory
namespace TopCatTrivialFibrationRecognitionTests

/-- Conditional client: the explicit simplicial-set hypothesis puts horn-RLP
weak equivalences in boundary-RLP maps. -/
theorem le_client
    (h : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    TopCat.realizedHornInclusions.{u}.rlp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedBoundaryInclusions.{u}.rlp :=
  TopCat.hornRLP_inf_W_le_boundaryRLP_of_sSet h

example
    (h : SSet.modelCategoryQuillen.J.{1}.rlp ⊓ SSet.KanComplex.W.{1} ≤
      SSet.modelCategoryQuillen.I.{1}.rlp) :
    TopCat.realizedHornInclusions.{1}.rlp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedBoundaryInclusions.{1}.rlp :=
  le_client h

example
    (h : SSet.modelCategoryQuillen.J.{0}.rlp ⊓ SSet.KanComplex.W.{0} ≤
      SSet.modelCategoryQuillen.I.{0}.rlp) :
    TopCat.realizedHornInclusions.{0}.rlp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedBoundaryInclusions.{0}.rlp :=
  le_client h

#print axioms TopCat.hornRLP_inf_W_le_boundaryRLP_of_sSet
#print axioms le_client

end TopCatTrivialFibrationRecognitionTests
end ModelCategory
end AlgebraicTopology
end MathlibExtTest
