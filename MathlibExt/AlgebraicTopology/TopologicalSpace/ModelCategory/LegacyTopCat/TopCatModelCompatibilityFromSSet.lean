/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.BoundaryRLPWeakHomotopyConditional
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatTrivialCofibrationRecognition

/-!
# Topological compatibility equalities from simplicial recognition

Let `H` and `B` be the realized horn and boundary inclusions on `TopCat.{u}`, and let `W`
denote weak homotopy equivalences. Assume `H.rlp.llp≤W` and `SSet.modelCategoryQuillen.J.rlp ⊓
SSet.KanComplex.W≤SSet.modelCategoryQuillen.I.rlp`. These inputs give `B.rlp.llp ⊓
W=H.rlp.llp`.

If, in addition, every simplicial boundary-right-lifting map between Kan complexes is a Kan
weak equivalence, then `H.rlp ⊓ W=B.rlp` also holds. The additional premise is explicitly
restricted to Kan source and target.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- In universe `u`, assume `TopCat.realizedHornInclusions.rlp.llp≤TopCat.weakHomotopyEquivalences`, assume every
`f:X→Y` between Kan simplicial sets with `SSet.modelCategoryQuillen.I.rlp f` lies in `SSet.KanComplex.W`, and assume
`SSet.modelCategoryQuillen.J.rlp ⊓ SSet.KanComplex.W≤SSet.modelCategoryQuillen.I.rlp`. Then
`TopCat.realizedHornInclusions.rlp ⊓ TopCat.weakHomotopyEquivalences = TopCat.realizedBoundaryInclusions.rlp`. -/
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

/-- In universe `u`, assume `TopCat.realizedHornInclusions.rlp.llp≤TopCat.weakHomotopyEquivalences` and
`SSet.modelCategoryQuillen.J.rlp ⊓ SSet.KanComplex.W≤SSet.modelCategoryQuillen.I.rlp`. Then
`TopCat.realizedBoundaryInclusions.rlp.llp ⊓ TopCat.weakHomotopyEquivalences = TopCat.realizedHornInclusions.rlp.llp`.
These are the two hypotheses for the cofibration equality. -/
theorem boundaryLLP_inf_W_eq_hornLLP_of_sSet
    (hHorn : realizedHornInclusions.{u}.rlp.llp ≤ weakHomotopyEquivalences)
    (hSSet : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    realizedBoundaryInclusions.{u}.rlp.llp ⊓ weakHomotopyEquivalences =
      realizedHornInclusions.{u}.rlp.llp :=
  boundaryLLP_inf_W_eq_hornLLP hHorn (hornRLP_inf_W_le_boundaryRLP_of_sSet hSSet)

end TopCat
