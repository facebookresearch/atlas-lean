/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DictionarySpec
import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.DictionarySpecTest

open Cslib.Algorithms.Lean.DictionarySpec

example :
    (bstSpec Nat).toFinset
        ((bstSpec Nat).insert 2 ((bstSpec Nat).insert 1 (bstSpec Nat).empty))
      = {1, 2} := by
  decide

example :
    (bstSpec Nat).mem 2
      ((bstSpec Nat).insert 2 ((bstSpec Nat).insert 1 (bstSpec Nat).empty)) := by
  exact OrderedSetSpec.mem_insert_self _ 2
    ((bstSpec Nat).inv_insert 1 (bstSpec Nat).inv_empty)

example :
    (bstSpec Nat).toFinset
        ((bstSpec Nat).delete 1
          ((bstSpec Nat).insert 2 ((bstSpec Nat).insert 1 (bstSpec Nat).empty)))
      = {2} := by
  decide

/-- Negative test: no ordered-set implementation on any state type can use
the identity as its insertion, since inserting into the empty state must
add the key to the abstraction. -/
example {S : Type} (spec : OrderedSetSpec Nat S) :
    spec.insert ≠ fun _ s => s := by
  intro h
  have e := spec.toFinset_insert 0 spec.inv_empty
  simp only [h] at e
  rw [spec.toFinset_empty] at e
  have hmem : (0 : Nat) ∈ (∅ : Finset Nat) := by
    rw [e]
    exact Finset.mem_insert_self 0 ∅
  exact Finset.notMem_empty 0 hmem

example :
    (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).mayContain 1
      ((bloomSpec ([fun _ : Nat => (0 : Fin 1)])).insert 1
        (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).empty) := by
  exact ApproxMembershipSpec.mayContain_insert_self _ 1
    (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).represents_empty

/-- False-positive example: with one bit and one constant hash, an element
that was never inserted is reported present. -/
example :
    (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).mayContain 2
      ((bloomSpec ([fun _ : Nat => (0 : Fin 1)])).insert 1
        (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).empty)
      ∧ (2 : Nat) ∉ ({1} : Finset Nat) := by
  exact ⟨rfl, by decide⟩

end Cslib.Algorithms.Lean.DictionarySpecTest

end
