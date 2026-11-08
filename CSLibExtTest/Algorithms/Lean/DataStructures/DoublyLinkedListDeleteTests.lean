/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Delete
public meta import Cslib.Algorithms.Lean.TimeM

/-!
# Whole-store deletion runtime fixtures
-/

@[expose] public meta section

open Cslib.Algorithms.Lean.DoublyLinkedList

open Cslib.Algorithms.Lean

universe u

namespace Cslib.Algorithms.Lean.DoublyLinkedList.DeleteTests

def verify {α : Type u} [DecidableEq α] [Repr α]
    (label : String) (actual expected : α) : IO Unit := do
  if actual ≠ expected then
    throw <| IO.userError s!"{label}: expected {repr expected}, actual {repr actual}"
  IO.println s!"{label}: {repr actual}"

public def main (args : List String) : IO Unit := do
  let singletonStore : Vector (Option (Node (Nat × String) (Fin 3))) 3 :=
    #v[some ⟨(9, "singleton"), none, none⟩, none,
      some ⟨(25, "detached"), some 2, some 2⟩]
  let singleton := listDelete singletonStore (some 0) 0 (by rfl)
    (by intro p he; cases he) (by intro n he; cases he)
  let wrongFreed := singletonStore.set 0 none
  verify "singleton complete allocated store and NIL header" singleton.ret
    (if args == ["wrong-free"] then wrongFreed else singletonStore, none)
  verify "singleton three source events" singleton.time 3
  let store : Vector (Option (Node (Nat × String) (Fin 3))) 3 :=
    #v[some ⟨(4, "head"), some 1, none⟩,
      some ⟨(9, "interior"), some 2, some 0⟩,
      some ⟨(16, "tail"), none, some 1⟩]
  let headResult := listDelete store (some 0) 0 (by rfl)
    (by intro p he; cases he) (by intro n he; cases Option.some.inj he; rfl)
  let headExpected : Vector (Option (Node (Nat × String) (Fin 3))) 3 :=
    #v[some ⟨(4, "head"), some 1, none⟩,
      some ⟨(9, "interior"), some 2, none⟩,
      some ⟨(16, "tail"), none, some 1⟩]
  verify "head complete store and updated header" headResult.ret
    (headExpected, if args == ["wrong-header"] then some 0 else some 1)
  verify "head four source events" headResult.time 4
  let middle := listDelete store (some 0) 1 (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let middleExpected : Vector (Option (Node (Nat × String) (Fin 3))) 3 :=
    #v[some ⟨(4, "head"), some 2, none⟩,
      some ⟨(9, "interior"), some 2, some 0⟩,
      some ⟨(16, "tail"), none, some 0⟩]
  let wrongBacklink := middleExpected.set 2 (some ⟨(16, "tail"), none, some 1⟩)
  verify "interior complete splice and unchanged removed record" middle.ret
    (if args == ["wrong-backlink"] then wrongBacklink else middleExpected, some 0)
  verify "interior four source events" middle.time 4
  let tailResult := listDelete store (some 0) 2 (by rfl)
    (by intro p he; cases Option.some.inj he; rfl) (by intro n he; cases he)
  let tailExpected : Vector (Option (Node (Nat × String) (Fin 3))) 3 :=
    #v[some ⟨(4, "head"), some 1, none⟩,
      some ⟨(9, "interior"), none, some 0⟩,
      some ⟨(16, "tail"), none, some 1⟩]
  verify "tail complete store and preserved head" tailResult.ret (tailExpected, some 0)
  verify "tail three source events" tailResult.time 3
  let duplicateStore : Vector (Option (Node (Nat × String) (Fin 3))) 3 :=
    #v[some ⟨(9, "first-nine"), some 1, none⟩,
      some ⟨(9, "selected-nine"), some 2, some 0⟩,
      some ⟨(9, "last-nine"), none, some 1⟩]
  let duplicate := listDelete duplicateStore (some 0) 1 (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let duplicateExpected : Vector (Option (Node (Nat × String) (Fin 3))) 3 :=
    #v[some ⟨(9, "first-nine"), some 2, none⟩,
      some ⟨(9, "selected-nine"), some 2, some 0⟩,
      some ⟨(9, "last-nine"), none, some 0⟩]
  verify "duplicate keys remove selected identity only" duplicate.ret (duplicateExpected, some 0)
  verify "duplicate-key four events" duplicate.time 4
  let disjointStore : Vector (Option (Node (Nat × String) (Fin 7))) 7 :=
    #v[some ⟨(4, "first-list-head"), some 1, none⟩,
      some ⟨(9, "first-list-interior"), some 2, some 0⟩,
      some ⟨(16, "first-list-tail"), none, some 1⟩,
      some ⟨(9, "second-list-head"), some 4, none⟩,
      some ⟨(9, "second-list-tail"), none, some 3⟩,
      none, some ⟨(25, "detached"), some 6, some 6⟩]
  let disjoint := listDelete disjointStore (some 0) 1 (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let disjointExpected : Vector (Option (Node (Nat × String) (Fin 7))) 7 :=
    #v[some ⟨(4, "first-list-head"), some 2, none⟩,
      some ⟨(9, "first-list-interior"), some 2, some 0⟩,
      some ⟨(16, "first-list-tail"), none, some 0⟩,
      some ⟨(9, "second-list-head"), some 4, none⟩,
      some ⟨(9, "second-list-tail"), none, some 3⟩,
      none, some ⟨(25, "detached"), some 6, some 6⟩]
  verify "disjoint second list, absent and detached cells" disjoint.ret (disjointExpected, some 0)
  verify "all allocations preserved" (disjoint.ret.1.map Option.isSome)
    (disjointStore.map Option.isSome)
  verify "all keys and satellites preserved" (disjoint.ret.1.map fun cell => cell.map Node.payload)
    (disjointStore.map fun cell => cell.map Node.payload)
  let aliasStore : Vector (Option (Node Nat (Fin 2))) 2 :=
    #v[some ⟨9, some 1, some 1⟩, some ⟨25, none, none⟩]
  let aliasResult := listDelete aliasStore none 0 (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let aliasExpected : Vector (Option (Node Nat (Fin 2))) 2 :=
    #v[some ⟨9, some 1, some 1⟩, some ⟨25, some 1, some 1⟩]
  verify "same predecessor/successor uses carried record" aliasResult.ret (aliasExpected, none)
  verify "aliased neighbour four events" aliasResult.time 4
  let selfStore : Vector (Option (Node Nat (Fin 1))) 1 := #v[some ⟨9, some 0, some 0⟩]
  let selfResult := listDelete selfStore (some 0) 0 (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  verify "self neighbours preserve every field" selfResult.ret (selfStore, some 0)
  verify "self neighbours four events" selfResult.time 4

#eval main []

end Cslib.Algorithms.Lean.DoublyLinkedList.DeleteTests
