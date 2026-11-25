/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractible

public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
# Weak contractibility of nerves: public API tests

These tests exercise the initial- and terminal-object weak-equivalence
corollaries at independent symbolic universes, at object universe one with
morphism universe zero, and at universe zero.  The concrete fixtures include
the walking initial and terminal categories and a one-object category.  An
empty-category negative gate prevents accidental removal of the required
initial or terminal hypothesis.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NerveContractible

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.NerveWeakContractibleTests

universe v u

variable {C : Type u} [Category.{v} C]

theorem symbolic_isInitial_client {X : C} (hX : IsInitial X) :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve C : SSet.{max u v})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_isInitial hX

theorem symbolic_isTerminal_client {Y : C} (hY : IsTerminal Y) :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve C : SSet.{max u v})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_isTerminal hY

theorem symbolic_hasInitial_client [HasInitial C] :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve C : SSet.{max u v})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_hasInitial

theorem symbolic_hasTerminal_client [HasTerminal C] :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve C : SSet.{max u v})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_hasTerminal

/-- A one-object category whose object universe is arbitrary and whose
morphisms remain in universe zero. -/
inductive OneObject : Type u
  | star

instance : Category.{0} OneObject.{u} where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

instance (X Y : OneObject.{u}) : Unique (X ⟶ Y) := by
  cases X
  cases Y
  change Unique PUnit
  infer_instance

instance oneObjectHasInitial : HasInitial OneObject.{u} :=
  hasInitial_of_unique .star

instance oneObjectHasTerminal : HasTerminal OneObject.{u} :=
  hasTerminal_of_unique .star

abbrev WalkingInitial := WithInitial OneObject.{u}

abbrev WalkingTerminal := WithTerminal OneObject.{u}

theorem walkingInitial_selected_u1 :
    SSet.realizationWeakEquivalences
      (terminal.from
        (nerve WalkingInitial.{1} : SSet.{1})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_isInitial
    WithInitial.starInitial

theorem walkingInitial_chosen_u1 :
    SSet.realizationWeakEquivalences
      (terminal.from
        (nerve WalkingInitial.{1} : SSet.{1})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_hasInitial

theorem walkingTerminal_selected_u1 :
    SSet.realizationWeakEquivalences
      (terminal.from
        (nerve WalkingTerminal.{1} : SSet.{1})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_isTerminal
    WithTerminal.starTerminal

theorem walkingTerminal_chosen_u1 :
    SSet.realizationWeakEquivalences
      (terminal.from
        (nerve WalkingTerminal.{1} : SSet.{1})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_hasTerminal

theorem oneObject_initial_u0 :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve OneObject.{0} : SSet.{0})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_hasInitial

theorem oneObject_terminal_u0 :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve OneObject.{0} : SSet.{0})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_hasTerminal

/-! ## Empty-category negative controls -/

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth HasInitial (Discrete PEmpty)

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth HasTerminal (Discrete PEmpty)

#print axioms
  NerveContractible.nerve_to_terminal_mem_realizationWeakEquivalences_of_isInitial
#print axioms
  NerveContractible.nerve_to_terminal_mem_realizationWeakEquivalences_of_isTerminal
#print axioms
  NerveContractible.nerve_to_terminal_mem_realizationWeakEquivalences_of_hasInitial
#print axioms
  NerveContractible.nerve_to_terminal_mem_realizationWeakEquivalences_of_hasTerminal

end MathlibExtTest.AlgebraicTopology.SimplicialSet.NerveWeakContractibleTests

end
