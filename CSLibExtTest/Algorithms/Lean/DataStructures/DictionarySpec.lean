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

example :
    (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).Represents
      ((bloomSpec ([fun _ : Nat => (0 : Fin 1)])).insert 1
        (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).empty) {1} := by
  exact (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).represents_insert 1
    (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).represents_empty

/-- Regression: the same state reports `2` present, yet it represents only
the inserted history, so it does not represent the empty set. -/
example :
    ¬ (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).Represents
      ((bloomSpec ([fun _ : Nat => (0 : Fin 1)])).insert 1
        (bloomSpec ([fun _ : Nat => (0 : Fin 1)])).empty) ∅ := by
  rintro ⟨l, hl, hfold⟩
  have hnil : l = [] := by
    cases l with
    | nil => rfl
    | cons a l' =>
      have hmem : a ∈ (a :: l').toFinset :=
        List.mem_toFinset.mpr (List.mem_cons.mpr (Or.inl rfl))
      rw [hl] at hmem
      exact absurd hmem (Finset.notMem_empty a)
  subst hnil
  rw [List.foldl_nil] at hfold
  have hfold' : BloomFilter.empty [fun _ : Nat => (0 : Fin 1)]
      = (BloomFilter.empty [fun _ : Nat => (0 : Fin 1)]).insert 1 := hfold
  have hfalse : (BloomFilter.empty [fun _ : Nat => (0 : Fin 1)]).mayContain 1
      = false :=
    BloomFilter.mayContain_empty (by simp) 1
  rw [hfold'] at hfalse
  have htrue := BloomFilter.mayContain_insert_self
    (BloomFilter.empty [fun _ : Nat => (0 : Fin 1)]) 1
  rw [hfalse] at htrue
  exact absurd htrue (by decide)

end Cslib.Algorithms.Lean.DictionarySpecTest

end
