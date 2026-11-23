/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatTrivialCofibrationRecognition

@[expose] public section

/-!
# Conditional trivial-cofibration recognition client

Thin public client for `TopCat.boundaryLLP_inf_W_le_hornLLP_of_sSet` by term
application only. Accepts the same explicit horn-cell-closure hypothesis
`TopCat.realizedHornInclusions.rlp.llp ≤ TopCat.weakHomotopyEquivalences` and
simplicial-set hypothesis
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
namespace TopCatTrivialCofibrationRecognitionTests

/-- Conditional client: the explicit horn-cell-closure and simplicial-set
hypotheses put boundary-LLP weak equivalences in horn-LLP maps. -/
theorem le_client
    (hHorn : TopCat.realizedHornInclusions.{u}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hSSet : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    TopCat.realizedBoundaryInclusions.{u}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedHornInclusions.{u}.rlp.llp :=
  TopCat.boundaryLLP_inf_W_le_hornLLP_of_sSet hHorn hSSet

example
    (hHorn : TopCat.realizedHornInclusions.{1}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hSSet : SSet.modelCategoryQuillen.J.{1}.rlp ⊓ SSet.KanComplex.W.{1} ≤
      SSet.modelCategoryQuillen.I.{1}.rlp) :
    TopCat.realizedBoundaryInclusions.{1}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedHornInclusions.{1}.rlp.llp :=
  le_client hHorn hSSet

example
    (hHorn : TopCat.realizedHornInclusions.{0}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hSSet : SSet.modelCategoryQuillen.J.{0}.rlp ⊓ SSet.KanComplex.W.{0} ≤
      SSet.modelCategoryQuillen.I.{0}.rlp) :
    TopCat.realizedBoundaryInclusions.{0}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedHornInclusions.{0}.rlp.llp :=
  le_client hHorn hSSet

#print axioms TopCat.boundaryLLP_inf_W_le_hornLLP_of_sSet
#print axioms le_client

end TopCatTrivialCofibrationRecognitionTests
end ModelCategory
end AlgebraicTopology
end MathlibExtTest
