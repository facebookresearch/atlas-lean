/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornCellWeakHomotopy

@[expose] public section

/-!
# Actual-cardinal conditional and final horn closure clients

Public clients retain the universe-zero actual-cardinal and sequential
conditional theorems, exercise actual-cardinal conditional closure at symbolic
and universe-one levels, and consume the final unconditional horn-left endpoint
at symbolic, universe-one, and universe-zero levels. The file also pins the
exact theorem-valued `NoMaxOrder` witness and rejects a global no-max instance,
a universe-one weak parent, and use of the sequential compatibility theorem to
explain the universe-one endpoint. It adds no instance, model structure, or KQ4
content.
-/

set_option autoImplicit false

universe u

open CategoryTheory MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCardinalWeakHomotopyTests

/-- Actual-cardinal per-diagram horn left-class client, forwarding the sole premise. -/
theorem horn_llp_cardinalOrd_perDiagram_client
    [(SSet.KanComplex.W :
      MorphismProperty SSet.{0}).IsStableUnderTransfiniteCompositionOfShape
      realizedGeneratorCardinal.{0}.ord.ToType] :
    TopCat.realizedHornInclusions.{0}.rlp.llp ≤ TopCat.weakHomotopyEquivalences :=
  TopCat.horn_llp_le_weakHomotopyEquivalences_of_cardinalOrd_perDiagram

/-- Sequential per-diagram horn left-class client, forwarding the sole premise. -/
theorem horn_llp_sequential_perDiagram_client
    [(SSet.KanComplex.W :
      MorphismProperty SSet.{0}).IsStableUnderTransfiniteCompositionOfShape
      ℕ] :
    TopCat.realizedHornInclusions.{0}.rlp.llp ≤ TopCat.weakHomotopyEquivalences :=
  TopCat.horn_llp_le_weakHomotopyEquivalences_of_sequential_perDiagram

/-- Symbolic actual-cardinal conditional horn closure. -/
theorem cardinalPerDiagram_symbolic
    [MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (SSet.KanComplex.W : MorphismProperty SSet.{u})
        realizedGeneratorCardinal.{u}.ord.ToType] :
    TopCat.realizedHornInclusions.{u}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences.{u} :=
  TopCat.horn_llp_le_weakHomotopyEquivalences_of_cardinalOrd_perDiagram

/-- Universe-one actual-cardinal conditional horn closure. -/
theorem cardinalPerDiagram_u1
    [MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (SSet.KanComplex.W : MorphismProperty SSet.{1})
        realizedGeneratorCardinal.{1}.ord.ToType] :
    TopCat.realizedHornInclusions.{1}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences.{1} :=
  TopCat.horn_llp_le_weakHomotopyEquivalences_of_cardinalOrd_perDiagram

/-- The exact no-maximum-order witness used locally by the final endpoint. -/
theorem actualCardinal_noMax_symbolic :
    NoMaxOrder realizedGeneratorCardinal.{u}.ord.ToType :=
  Cardinal.noMaxOrder
    (Cardinal.aleph0_le_continuum.trans
      (le_of_lt (Order.lt_succ Cardinal.continuum)))

/-- Final actual-cardinal horn closure at a symbolic universe. -/
theorem endpoint_symbolic :
    TopCat.realizedHornInclusions.{u}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences.{u} :=
  TopCat.horn_llp_le_weakHomotopyEquivalences

/-- Final actual-cardinal horn closure at universe one. -/
theorem endpoint_u1 :
    TopCat.realizedHornInclusions.{1}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences.{1} :=
  TopCat.horn_llp_le_weakHomotopyEquivalences

/-- Final endpoint's original universe-zero specialization. -/
theorem endpoint_u0 :
    TopCat.realizedHornInclusions.{0}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences.{0} :=
  TopCat.horn_llp_le_weakHomotopyEquivalences

/-- The actual-cardinal no-max witness and weak parent remain non-global. -/
example : True := by
  fail_if_success
    let _ : NoMaxOrder
      realizedGeneratorCardinal.{1}.ord.ToType := inferInstance
  fail_if_success
    let _ : CategoryWithWeakEquivalences TopCat.{1} := inferInstance
  trivial

/-- The retained sequential compatibility theorem cannot prove the u1 endpoint. -/
example
    [MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (SSet.KanComplex.W : MorphismProperty SSet.{0}) ℕ] :
    True := by
  fail_if_success
    have _h :
        TopCat.realizedHornInclusions.{1}.rlp.llp ≤
          TopCat.weakHomotopyEquivalences.{1} :=
      TopCat.horn_llp_le_weakHomotopyEquivalences_of_sequential_perDiagram
  trivial

#print axioms TopCat.horn_llp_le_weakHomotopyEquivalences_of_cardinalOrd_perDiagram
#print axioms TopCat.horn_llp_le_weakHomotopyEquivalences
#print axioms horn_llp_cardinalOrd_perDiagram_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornCardinalWeakHomotopyTests
