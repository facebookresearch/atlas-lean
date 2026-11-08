/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SkipList.Erase
public import Mathlib.Data.Nat.Basic

/-!
# Skip-list erasure API tests

Ordinary importing proofs exercise each public equation and semantic law.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SkipListEraseAPITests

open SkipList

universe u v

public theorem empty_equation_fixture {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) : erase key (empty : SkipList α β) = empty :=
  erase_empty key

public theorem early_stop_equation_fixture {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {entry : Entry α β} {entries : List (Entry α β)}
    (before : key < entry.key) :
    (erase key ⟨entry :: entries⟩).entries = entry :: entries :=
  erase_cons_of_lt before

public theorem recurse_equation_fixture {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {entry : Entry α β} {entries : List (Entry α β)}
    (after : entry.key < key) :
    (erase key ⟨entry :: entries⟩).entries =
      entry :: (erase key ⟨entries⟩).entries :=
  erase_cons_of_gt after

public theorem matching_equation_fixture {α : Type u} {β : Type v} [LinearOrder α]
    {key : α} {entry : Entry α β} {entries : List (Entry α β)}
    (matching : key = entry.key) :
    (erase key ⟨entry :: entries⟩).entries = entries :=
  erase_cons_of_eq matching

public def populated : SkipList Nat String :=
  insert 4 "four" 4 <|
    insert 1 "one" 1 <|
      insert 3 "three" 2 <|
        insert 2 "two" 3 empty

public theorem populated_valid : Valid populated :=
  valid_insert (valid_insert (valid_insert (valid_insert valid_empty)))

public theorem erase_middle_fixture :
    (erase 2 populated).entries =
      [{ key := 1, value := "one", height := 1 },
        { key := 3, value := "three", height := 2 },
        { key := 4, value := "four", height := 4 }] := by
  decide

example {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (list : SkipList α β) (valid : Valid list) :
    (erase key list).entries =
      list.entries.filter (fun entry => decide (entry.key ≠ key)) :=
  erase_entries_filter valid

example {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (list : SkipList α β) (valid : Valid list) :
    Valid (erase key list) :=
  valid_erase valid

example {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (list : SkipList α β) (valid : Valid list) :
    lookup key (erase key list) = none :=
  lookup_erase valid

example {α : Type u} {β : Type v} [LinearOrder α]
    (key other : α) (list : SkipList α β) (valid : Valid list)
    (different : other ≠ key) :
    lookup other (erase key list) = lookup other list :=
  lookup_erase_of_ne valid different

example {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (list : SkipList α β) (valid : Valid list) :
    heightOf key (erase key list) = none :=
  heightOf_erase valid

example {α : Type u} {β : Type v} [LinearOrder α]
    (key other : α) (list : SkipList α β) (valid : Valid list)
    (different : other ≠ key) :
    heightOf other (erase key list) = heightOf other list :=
  heightOf_erase_of_ne valid different

example {α : Type u} {β : Type v} [LinearOrder α]
    (key : α) (list : SkipList α β) (valid : Valid list) (index : Nat) :
    level index (erase key list) =
      (level index list).filter (fun pair => decide (pair.1 ≠ key)) :=
  level_erase valid index

#check erase
#check erase_empty
#check erase_cons_of_lt
#check erase_cons_of_gt
#check erase_cons_of_eq
#check erase_entries_filter
#check valid_erase
#check lookup_erase
#check lookup_erase_of_ne
#check heightOf_erase
#check heightOf_erase_of_ne
#check level_erase

#print axioms erase_empty
#print axioms erase_cons_of_lt
#print axioms erase_cons_of_gt
#print axioms erase_cons_of_eq
#print axioms erase_entries_filter
#print axioms valid_erase
#print axioms lookup_erase
#print axioms lookup_erase_of_ne
#print axioms heightOf_erase
#print axioms heightOf_erase_of_ne
#print axioms level_erase
#print axioms empty_equation_fixture
#print axioms early_stop_equation_fixture
#print axioms recurse_equation_fixture
#print axioms matching_equation_fixture
#print axioms populated_valid
#print axioms erase_middle_fixture

end Cslib.Algorithms.Lean.SkipListEraseAPITests
