/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelCompatibilityFromSSet

@[expose] public section

/-!
# TopCat compatibility from simplicial inputs clients

Thin public clients for both recognition equalities in
`TopCatModelCompatibilityFromSSet` by term application only. Each client
forwards every explicit premise unchanged. Supplies no premise, adds no
instance, and claims no unconditional model structure.
-/

set_option autoImplicit false

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatModelCompatibilityFromSSetTests

/-- Fibration equality client, forwarding all three premises unchanged. -/
theorem hornRLP_inf_W_eq_boundaryRLP_client
    (hHorn : TopCat.realizedHornInclusions.{u}.rlp.llp ≤ TopCat.weakHomotopyEquivalences)
    (hI : ∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f)
    (hSSet : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    TopCat.realizedHornInclusions.{u}.rlp ⊓ TopCat.weakHomotopyEquivalences =
      TopCat.realizedBoundaryInclusions.{u}.rlp :=
  TopCat.hornRLP_inf_W_eq_boundaryRLP_of_sSet hHorn hI hSSet

/-- Cofibration equality client, forwarding both premises unchanged. -/
theorem boundaryLLP_inf_W_eq_hornLLP_client
    (hHorn : TopCat.realizedHornInclusions.{u}.rlp.llp ≤ TopCat.weakHomotopyEquivalences)
    (hSSet : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    TopCat.realizedBoundaryInclusions.{u}.rlp.llp ⊓ TopCat.weakHomotopyEquivalences =
      TopCat.realizedHornInclusions.{u}.rlp.llp :=
  TopCat.boundaryLLP_inf_W_eq_hornLLP_of_sSet hHorn hSSet

section UniverseOne

example
    (hHorn : TopCat.realizedHornInclusions.{1}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hI : ∀ {X Y : SSet.{1}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{1}.rlp f → SSet.KanComplex.W.{1} f)
    (hSSet : SSet.modelCategoryQuillen.J.{1}.rlp ⊓ SSet.KanComplex.W.{1} ≤
      SSet.modelCategoryQuillen.I.{1}.rlp) :
    TopCat.realizedHornInclusions.{1}.rlp ⊓ TopCat.weakHomotopyEquivalences =
      TopCat.realizedBoundaryInclusions.{1}.rlp :=
  hornRLP_inf_W_eq_boundaryRLP_client hHorn hI hSSet

example
    (hHorn : TopCat.realizedHornInclusions.{1}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hSSet : SSet.modelCategoryQuillen.J.{1}.rlp ⊓ SSet.KanComplex.W.{1} ≤
      SSet.modelCategoryQuillen.I.{1}.rlp) :
    TopCat.realizedBoundaryInclusions.{1}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences = TopCat.realizedHornInclusions.{1}.rlp.llp :=
  boundaryLLP_inf_W_eq_hornLLP_client hHorn hSSet

end UniverseOne

section UniverseZero

example
    (hHorn : TopCat.realizedHornInclusions.{0}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hI : ∀ {X Y : SSet.{0}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{0}.rlp f → SSet.KanComplex.W.{0} f)
    (hSSet : SSet.modelCategoryQuillen.J.{0}.rlp ⊓ SSet.KanComplex.W.{0} ≤
      SSet.modelCategoryQuillen.I.{0}.rlp) :
    TopCat.realizedHornInclusions.{0}.rlp ⊓ TopCat.weakHomotopyEquivalences =
      TopCat.realizedBoundaryInclusions.{0}.rlp :=
  hornRLP_inf_W_eq_boundaryRLP_client hHorn hI hSSet

example
    (hHorn : TopCat.realizedHornInclusions.{0}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hSSet : SSet.modelCategoryQuillen.J.{0}.rlp ⊓ SSet.KanComplex.W.{0} ≤
      SSet.modelCategoryQuillen.I.{0}.rlp) :
    TopCat.realizedBoundaryInclusions.{0}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences = TopCat.realizedHornInclusions.{0}.rlp.llp :=
  boundaryLLP_inf_W_eq_hornLLP_client hHorn hSSet

end UniverseZero

#print axioms TopCat.hornRLP_inf_W_eq_boundaryRLP_of_sSet
#print axioms TopCat.boundaryLLP_inf_W_eq_hornLLP_of_sSet
#print axioms hornRLP_inf_W_eq_boundaryRLP_client
#print axioms boundaryLLP_inf_W_eq_hornLLP_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatModelCompatibilityFromSSetTests
