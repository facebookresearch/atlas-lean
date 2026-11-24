/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.BoundaryRLPWeakHomotopyConditional
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatTrivialCofibrationRecognition

/-!
# TopCat compatibility equalities from simplicial-set inputs

This file is part of the KQ3 layer. From exactly the three explicit inputs
`realizedHornInclusions.rlp.llp ≤ weakHomotopyEquivalences`,
`∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f`, and
`SSet.modelCategoryQuillen.J.rlp ⊓ SSet.KanComplex.W ≤
SSet.modelCategoryQuillen.I.rlp`, it derives both TopCat recognition equalities
`realizedHornInclusions.rlp ⊓ weakHomotopyEquivalences =
realizedBoundaryInclusions.rlp` and
`realizedBoundaryInclusions.rlp.llp ⊓ weakHomotopyEquivalences =
realizedHornInclusions.rlp.llp`.

Each equality reuses the staged providers with no proof duplicated here: the
boundary bridge
`boundaryRLP_le_weakHomotopyEquivalences_of_kanRestricted_Irlp_le_W`, the
direct recognition `hornRLP_inf_W_le_boundaryRLP_of_sSet`, the cofibration
recognition `boundaryLLP_inf_W_le_hornLLP_of_sSet`, and the conditional
equalities `hornRLP_inf_W_eq_boundaryRLP` and `boundaryLLP_inf_W_eq_hornLLP`.
No input is supplied here and no model structure is built. The `I.rlp`
premise is Kan-restricted and dependency-forward: identities on non-Kan
simplicial sets lie in `I.rlp` but not in `KanComplex.W`, so no universal
`I.rlp ≤ W` is claimed and no build is claimed here.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- Fibration equality from the three explicit inputs, with the Kan-restricted
`I.rlp` premise. -/
theorem hornRLP_inf_W_eq_boundaryRLP_of_sSet
    (hHorn : realizedHornInclusions.{u}.rlp.llp ≤ weakHomotopyEquivalences)
    (hI : ∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f)
    (hSSet : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    realizedHornInclusions.{u}.rlp ⊓ weakHomotopyEquivalences =
      realizedBoundaryInclusions.{u}.rlp :=
  hornRLP_inf_W_eq_boundaryRLP
    (boundaryRLP_le_weakHomotopyEquivalences_of_kanRestricted_Irlp_le_W hI)
    (boundaryLLP_inf_W_le_hornLLP_of_sSet hHorn hSSet)

/-- Cofibration equality from horn-cell closure and simplicial recognition. -/
theorem boundaryLLP_inf_W_eq_hornLLP_of_sSet
    (hHorn : realizedHornInclusions.{u}.rlp.llp ≤ weakHomotopyEquivalences)
    (hSSet : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences =
      realizedHornInclusions.{u}.rlp.llp :=
  boundaryLLP_inf_W_eq_hornLLP hHorn (hornRLP_inf_W_le_boundaryRLP_of_sSet hSSet)

end TopCat
