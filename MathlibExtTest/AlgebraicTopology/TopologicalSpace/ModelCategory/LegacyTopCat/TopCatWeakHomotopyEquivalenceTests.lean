/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

@[expose] public section

/-!
# TopCat weak-homotopy-equivalence property client

Compile-time consumer checks for `TopCat.weakHomotopyEquivalences`
inverse-image packaging: the membership unfolding plus the three inherited
closure instances (two-out-of-three, retract stability, respects-isomorphisms).
The symbolic packet also confirms no global universe-one singular-Kan
instance. It states no `ContainsIdentities`, weak category, model structure,
product closure, or SSet weak-equivalence claim.
-/

set_option autoImplicit false

universe u

open CategoryTheory MorphismProperty

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatWeakHomotopyEquivalenceTests

section Membership

theorem mem_client {X Y : TopCat.{0}} (f : X ⟶ Y) :
    TopCat.weakHomotopyEquivalences f ↔ SSet.KanComplex.W (TopCat.toSSet.map f) :=
  TopCat.mem_weakHomotopyEquivalences_iff f

#print axioms TopCat.weakHomotopyEquivalences
#print axioms TopCat.mem_weakHomotopyEquivalences_iff
#print axioms mem_client

end Membership

section TwoOutOfThree

theorem twoOutOfThree_client :
    TopCat.weakHomotopyEquivalences.HasTwoOutOfThreeProperty :=
  inferInstance

#print axioms TopCat.hasTwoOutOfThreeProperty
#print axioms twoOutOfThree_client

end TwoOutOfThree

section RetractStability

theorem retracts_client :
    TopCat.weakHomotopyEquivalences.IsStableUnderRetracts :=
  inferInstance

#print axioms TopCat.isStableUnderRetracts
#print axioms retracts_client

end RetractStability

section RespectsIso

theorem respectsIso_client :
    TopCat.weakHomotopyEquivalences.RespectsIso :=
  inferInstance

#print axioms TopCat.respectsIso
#print axioms respectsIso_client

end RespectsIso

section SymbolicUniverse

theorem mem_symbolic {X Y : TopCat.{u}} (f : X ⟶ Y) :
    TopCat.weakHomotopyEquivalences f ↔
      SSet.KanComplex.W (TopCat.toSSet.map f) :=
  TopCat.mem_weakHomotopyEquivalences_iff f

theorem twoOutOfThree_symbolic :
    TopCat.weakHomotopyEquivalences.{u}.HasTwoOutOfThreeProperty :=
  inferInstance

theorem retracts_symbolic :
    TopCat.weakHomotopyEquivalences.{u}.IsStableUnderRetracts :=
  inferInstance

theorem respectsIso_symbolic :
    TopCat.weakHomotopyEquivalences.{u}.RespectsIso :=
  inferInstance

theorem respectsIso_u1 :
    TopCat.weakHomotopyEquivalences.{1}.RespectsIso :=
  inferInstance

example (_X : TopCat.{1}) : True := by
  fail_if_success
    let _ : SSet.KanComplex (TopCat.toSSet.obj _X) := inferInstance
  trivial

end SymbolicUniverse

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatWeakHomotopyEquivalenceTests
