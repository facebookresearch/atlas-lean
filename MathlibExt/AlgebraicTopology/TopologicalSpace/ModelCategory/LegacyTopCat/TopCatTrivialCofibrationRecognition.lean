/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelCompatibilityConditional
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatTrivialFibrationRecognition

/-!
# Conditional trivial-cofibration recognition for realized horns in `TopCat`

This file is part of the KQ3 layer. It proves the second remaining cross
inclusion directly by composing the two staged inputs, with no proof
duplicated here: the singular/realization transport
`TopCat.hornRLP_inf_W_le_boundaryRLP_of_sSet` turns the external simplicial
recognition hypothesis
`SSet.modelCategoryQuillen.J.rlp ⊓ SSet.KanComplex.W ≤
SSet.modelCategoryQuillen.I.rlp` into the fibration cross inclusion, and the
staged retract theorem `TopCat.boundaryLLP_inf_W_le_hornLLP` turns that plus
the KQ3 horn-cell closure hypothesis
`realizedHornInclusions.rlp.llp ≤ weakHomotopyEquivalences` into the target
cofibration cross inclusion.

This proves only the stated conditional inclusion. It does not supply either
hypothesis, and claims no reverse inclusion, no equality, and no model
structure. It assumes neither the target inclusion nor a model structure.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- Conditional recognition: boundary left-class weak equivalences are horn
left-class maps, from horn-cell closure and simplicial recognition. -/
theorem boundaryLLP_inf_W_le_hornLLP_of_sSet
    (hHorn : realizedHornInclusions.{u}.rlp.llp ≤ weakHomotopyEquivalences)
    (hSSet : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences ≤
      realizedHornInclusions.{u}.rlp.llp :=
  boundaryLLP_inf_W_le_hornLLP hHorn (hornRLP_inf_W_le_boundaryRLP_of_sSet hSSet)

end TopCat
