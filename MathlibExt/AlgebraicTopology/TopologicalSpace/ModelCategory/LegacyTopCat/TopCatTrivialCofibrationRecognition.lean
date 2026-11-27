/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelCompatibilityConditional
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatTrivialFibrationRecognition

/-!
# Topological cofibration recognition from simplicial lifting

Assume the horn-generated left class on `TopCat.{u}` consists of weak homotopy equivalences,
and assume `J.rlp ⊓ KanComplex.W ≤ I.rlp` on `SSet.{u}`. The realization–singular lifting
transport and the retract argument give `realizedBoundaryInclusions.rlp.llp ⊓
weakHomotopyEquivalences ≤ realizedHornInclusions.rlp.llp`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- Assume `TopCat.realizedHornInclusions.{u}.rlp.llp ≤ TopCat.weakHomotopyEquivalences` and
`SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤ SSet.modelCategoryQuillen.I.{u}.rlp`. Then
`TopCat.realizedBoundaryInclusions.{u}.rlp.llp ⊓ TopCat.weakHomotopyEquivalences ≤
TopCat.realizedHornInclusions.{u}.rlp.llp`.
The conclusion is the stated topological cofibration cross inclusion. -/
theorem boundaryLLP_inf_W_le_hornLLP_of_sSet
    (hHorn : realizedHornInclusions.{u}.rlp.llp ≤ weakHomotopyEquivalences)
    (hSSet : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences ≤
      realizedHornInclusions.{u}.rlp.llp :=
  boundaryLLP_inf_W_le_hornLLP hHorn (hornRLP_inf_W_le_boundaryRLP_of_sSet hSSet)

end TopCat
