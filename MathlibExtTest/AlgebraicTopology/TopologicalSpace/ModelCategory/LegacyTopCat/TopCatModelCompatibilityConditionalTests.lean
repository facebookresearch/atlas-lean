/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelCompatibilityConditional

@[expose] public section

/-!
# Conditional TopCat model compatibility client tests

Thin public clients for the four conditional inclusion/equality theorems in
`TopCatModelCompatibilityConditional`, by term application only. Each client
forwards every explicit hard-inclusion/cross-inclusion hypothesis unchanged.
Supplies no premise, adds no instance, and claims no unconditional model
structure.
-/

set_option autoImplicit false

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatModelCompatibilityConditionalTests

/-- Fibration retract-step client, forwarding both hypotheses unchanged. -/
theorem hornRLP_inf_W_le_boundaryRLP_client
    (hBdry : TopCat.realizedBoundaryInclusions.{u}.rlp ≤ TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedBoundaryInclusions.{u}.rlp.llp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedHornInclusions.{u}.rlp.llp) :
    TopCat.realizedHornInclusions.{u}.rlp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedBoundaryInclusions.{u}.rlp :=
  TopCat.hornRLP_inf_W_le_boundaryRLP hBdry hCross

/-- Cofibration retract-step client, forwarding both hypotheses unchanged. -/
theorem boundaryLLP_inf_W_le_hornLLP_client
    (hHorn : TopCat.realizedHornInclusions.{u}.rlp.llp ≤ TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedHornInclusions.{u}.rlp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedBoundaryInclusions.{u}.rlp) :
    TopCat.realizedBoundaryInclusions.{u}.rlp.llp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedHornInclusions.{u}.rlp.llp :=
  TopCat.boundaryLLP_inf_W_le_hornLLP hHorn hCross

/-- Conditional fibration equality client, forwarding both hypotheses unchanged. -/
theorem hornRLP_inf_W_eq_boundaryRLP_client
    (hBdry : TopCat.realizedBoundaryInclusions.{u}.rlp ≤ TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedBoundaryInclusions.{u}.rlp.llp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedHornInclusions.{u}.rlp.llp) :
    TopCat.realizedHornInclusions.{u}.rlp ⊓ TopCat.weakHomotopyEquivalences =
      TopCat.realizedBoundaryInclusions.{u}.rlp :=
  TopCat.hornRLP_inf_W_eq_boundaryRLP hBdry hCross

/-- Conditional cofibration equality client, forwarding both hypotheses unchanged. -/
theorem boundaryLLP_inf_W_eq_hornLLP_client
    (hHorn : TopCat.realizedHornInclusions.{u}.rlp.llp ≤ TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedHornInclusions.{u}.rlp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedBoundaryInclusions.{u}.rlp) :
    TopCat.realizedBoundaryInclusions.{u}.rlp.llp ⊓ TopCat.weakHomotopyEquivalences =
      TopCat.realizedHornInclusions.{u}.rlp.llp :=
  TopCat.boundaryLLP_inf_W_eq_hornLLP hHorn hCross

section UniverseOne

example
    (hBdry : TopCat.realizedBoundaryInclusions.{1}.rlp ≤
      TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedBoundaryInclusions.{1}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences ≤ TopCat.realizedHornInclusions.{1}.rlp.llp) :
    TopCat.realizedHornInclusions.{1}.rlp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedBoundaryInclusions.{1}.rlp :=
  hornRLP_inf_W_le_boundaryRLP_client hBdry hCross

example
    (hHorn : TopCat.realizedHornInclusions.{1}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedHornInclusions.{1}.rlp ⊓
      TopCat.weakHomotopyEquivalences ≤ TopCat.realizedBoundaryInclusions.{1}.rlp) :
    TopCat.realizedBoundaryInclusions.{1}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences ≤ TopCat.realizedHornInclusions.{1}.rlp.llp :=
  boundaryLLP_inf_W_le_hornLLP_client hHorn hCross

example
    (hBdry : TopCat.realizedBoundaryInclusions.{1}.rlp ≤
      TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedBoundaryInclusions.{1}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences ≤ TopCat.realizedHornInclusions.{1}.rlp.llp) :
    TopCat.realizedHornInclusions.{1}.rlp ⊓ TopCat.weakHomotopyEquivalences =
      TopCat.realizedBoundaryInclusions.{1}.rlp :=
  hornRLP_inf_W_eq_boundaryRLP_client hBdry hCross

example
    (hHorn : TopCat.realizedHornInclusions.{1}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedHornInclusions.{1}.rlp ⊓
      TopCat.weakHomotopyEquivalences ≤ TopCat.realizedBoundaryInclusions.{1}.rlp) :
    TopCat.realizedBoundaryInclusions.{1}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences = TopCat.realizedHornInclusions.{1}.rlp.llp :=
  boundaryLLP_inf_W_eq_hornLLP_client hHorn hCross

end UniverseOne

section UniverseZero

example
    (hBdry : TopCat.realizedBoundaryInclusions.{0}.rlp ≤
      TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedBoundaryInclusions.{0}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences ≤ TopCat.realizedHornInclusions.{0}.rlp.llp) :
    TopCat.realizedHornInclusions.{0}.rlp ⊓ TopCat.weakHomotopyEquivalences ≤
      TopCat.realizedBoundaryInclusions.{0}.rlp :=
  hornRLP_inf_W_le_boundaryRLP_client hBdry hCross

example
    (hHorn : TopCat.realizedHornInclusions.{0}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedHornInclusions.{0}.rlp ⊓
      TopCat.weakHomotopyEquivalences ≤ TopCat.realizedBoundaryInclusions.{0}.rlp) :
    TopCat.realizedBoundaryInclusions.{0}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences ≤ TopCat.realizedHornInclusions.{0}.rlp.llp :=
  boundaryLLP_inf_W_le_hornLLP_client hHorn hCross

example
    (hBdry : TopCat.realizedBoundaryInclusions.{0}.rlp ≤
      TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedBoundaryInclusions.{0}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences ≤ TopCat.realizedHornInclusions.{0}.rlp.llp) :
    TopCat.realizedHornInclusions.{0}.rlp ⊓ TopCat.weakHomotopyEquivalences =
      TopCat.realizedBoundaryInclusions.{0}.rlp :=
  hornRLP_inf_W_eq_boundaryRLP_client hBdry hCross

example
    (hHorn : TopCat.realizedHornInclusions.{0}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences)
    (hCross : TopCat.realizedHornInclusions.{0}.rlp ⊓
      TopCat.weakHomotopyEquivalences ≤ TopCat.realizedBoundaryInclusions.{0}.rlp) :
    TopCat.realizedBoundaryInclusions.{0}.rlp.llp ⊓
      TopCat.weakHomotopyEquivalences = TopCat.realizedHornInclusions.{0}.rlp.llp :=
  boundaryLLP_inf_W_eq_hornLLP_client hHorn hCross

end UniverseZero

#print axioms TopCat.hornRLP_inf_W_le_boundaryRLP
#print axioms TopCat.boundaryLLP_inf_W_le_hornLLP
#print axioms TopCat.hornRLP_inf_W_eq_boundaryRLP
#print axioms TopCat.boundaryLLP_inf_W_eq_hornLLP
#print axioms hornRLP_inf_W_le_boundaryRLP_client
#print axioms boundaryLLP_inf_W_le_hornLLP_client
#print axioms hornRLP_inf_W_eq_boundaryRLP_client
#print axioms boundaryLLP_inf_W_eq_hornLLP_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatModelCompatibilityConditionalTests
