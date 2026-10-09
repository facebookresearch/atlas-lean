/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Basic
public meta import Cslib.Algorithms.Lean.TimeM

/-! Whole-store, neighbour, frame, satellite and source-order prepend fixtures. -/

@[expose] public meta section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DoublyLinkedList.PrependTests

universe u

private def check {α : Type u} [DecidableEq α] [Repr α]
    (label : String) (actual expected : α) : IO Unit := do
  if actual ≠ expected then
    throw <| IO.userError s!"{label}: expected {repr expected}, actual {repr actual}"
  IO.println s!"{label}: {repr actual}"

private def follow {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (pointer : Node α (Fin capacity) → Option (Fin capacity))
    (fuel : Nat) (head : Option (Fin capacity)) : List (Fin capacity) :=
  match fuel, head with
  | 0, _ => []
  | _, none => []
  | fuel + 1, some h => h :: follow store pointer fuel ((store.get h).bind pointer)

private def runCases (args : List String) : IO Unit := do
  let emptyStore : Vector (Option (Node Nat (Fin 1))) 1 :=
    #v[some ⟨25, some 0, some 0⟩]
  let empty := listPrepend emptyStore none 0 (by rfl) (by intro h he; cases he)
  let emptyExpected : Vector (Option (Node Nat (Fin 1))) 1 := #v[some ⟨25, none, none⟩]
  check "empty whole store and head" empty.ret (emptyExpected, some 0)
  check "empty four pointer/test events" empty.time
    (if args == ["wrong-count"] then 3 else 4)
  let store : Vector (Option (Node Nat (Fin 3))) 3 :=
    #v[some ⟨9, none, none⟩, some ⟨25, some 2, some 2⟩, some ⟨77, some 2, some 2⟩]
  let nonempty := listPrepend store (some 0) 1 (by rfl) (by
    intro h he
    cases Option.some.inj he
    rfl)
  let nonemptyExpected : Vector (Option (Node Nat (Fin 3))) 3 :=
    #v[some ⟨9, none, some 1⟩, some ⟨25, some 0, none⟩, some ⟨77, some 2, some 2⟩]
  check "nonempty whole store and foreign cell" nonempty.ret (nonemptyExpected, some 1)
  check "nonempty five pointer/test events" nonempty.time 5
  let clrs : Vector (Option (Node (Nat × String) (Fin 10))) 10 :=
    #v[some ⟨(4, "four"), some 6, some 4⟩,
      some ⟨(9, "nine"), some 4, none⟩,
      some ⟨(9, "other-nine-a"), some 5, none⟩,
      some ⟨(25, "new-twenty-five"), some 2, some 9⟩,
      some ⟨(16, "sixteen"), some 0, some 1⟩,
      some ⟨(9, "other-nine-b"), none, some 2⟩,
      some ⟨(1, "one"), none, some 0⟩,
      none,
      some ⟨(25, "second-twenty-five"), some 9, some 2⟩,
      some ⟨(25, "foreign-twenty-five"), some 9, some 9⟩]
  let clrsResult := listPrepend clrs (some 1) 3 (by rfl) (by
    intro h he
    cases Option.some.inj he
    rfl)
  let clrsExpected : Vector (Option (Node (Nat × String) (Fin 10))) 10 :=
    #v[some ⟨(4, "four"), some 6, some 4⟩,
      some ⟨(9, "nine"), some 4, some 3⟩,
      some ⟨(9, "other-nine-a"), some 5, none⟩,
      some ⟨(25, "new-twenty-five"), some 1, none⟩,
      some ⟨(16, "sixteen"), some 0, some 1⟩,
      some ⟨(9, "other-nine-b"), none, some 2⟩,
      some ⟨(1, "one"), none, some 0⟩,
      none,
      some ⟨(25, "second-twenty-five"), some 9, some 2⟩,
      some ⟨(25, "foreign-twenty-five"), some 9, some 9⟩]
  check "CLRS initial forward identities" (follow clrs Node.next 10 (some 1)) [1, 4, 0, 6]
  check "CLRS complete ten-cell saved store and header" clrsResult.ret
    (clrsExpected, if args == ["wrong-head"] then some 1 else some 3)
  check "CLRS five events" clrsResult.time 5
  check "CLRS forward identities" (follow clrsResult.ret.1 Node.next 10 clrsResult.ret.2)
    [3, 1, 4, 0, 6]
  check "CLRS backward identities" (follow clrsResult.ret.1 Node.prev 10 (some 6)) [6, 0, 4, 1, 3]
  check "CLRS keys and satellites" ((follow clrsResult.ret.1 Node.next 10 clrsResult.ret.2).map
    fun i => (clrsResult.ret.1.get i).map Node.payload)
    [some (25, "new-twenty-five"), some (9, "nine"), some (16, "sixteen"),
      some (4, "four"), some (1, "one")]
  check "disjoint duplicate-key list forward" (follow clrsResult.ret.1 Node.next 10 (some 2)) [2, 5]
  check "disjoint duplicate-key list backward"
    (follow clrsResult.ret.1 Node.prev 10 (some 5)) [5, 2]
  check "absent cell remains absent" (clrsResult.ret.1.get 7) none
  check "all ten payloads preserved" (clrsResult.ret.1.map fun cell => cell.map Node.payload)
    (clrs.map fun cell => cell.map Node.payload)
  check "all ten allocation statuses preserved" (clrsResult.ret.1.map Option.isSome)
    (clrs.map Option.isSome)
  let second := listPrepend clrsResult.ret.1 clrsResult.ret.2 8 (by rfl) (by
    intro h he
    cases Option.some.inj he
    rfl)
  let secondExpected : Vector (Option (Node (Nat × String) (Fin 10))) 10 :=
    #v[some ⟨(4, "four"), some 6, some 4⟩,
      some ⟨(9, "nine"), some 4, some 3⟩,
      some ⟨(9, "other-nine-a"), some 5, none⟩,
      some ⟨(25, "new-twenty-five"), some 1, some 8⟩,
      some ⟨(16, "sixteen"), some 0, some 1⟩,
      some ⟨(9, "other-nine-b"), none, some 2⟩,
      some ⟨(1, "one"), none, some 0⟩,
      none,
      some ⟨(25, "second-twenty-five"), some 3, none⟩,
      some ⟨(25, "foreign-twenty-five"), some 9, some 9⟩]
  check "second prepend uses actual first saved output" second.ret (secondExpected, some 8)
  check "two same-run event totals" (clrsResult.time + second.time) 10
  check "second prepend forward identities" (follow second.ret.1 Node.next 10 second.ret.2)
    [8, 3, 1, 4, 0, 6]
  check "second prepend backward identities" (follow second.ret.1 Node.prev 10 (some 6))
    [6, 0, 4, 1, 3, 8]
  let aliasStore : Vector (Option (Node Nat (Fin 2))) 2 :=
    #v[some ⟨25, some 1, some 1⟩, some ⟨77, none, none⟩]
  let aliasResult := listPrepend aliasStore (some 0) 0 (by rfl) (by
    intro h he
    cases Option.some.inj he
    rfl)
  let aliasExpected : Vector (Option (Node Nat (Fin 2))) 2 :=
    #v[some ⟨25, if args == ["wrong-alias-next"] then some 1 else some 0,
      if args == ["wrong-alias-prev"] then none else some 0⟩, some ⟨77, none, none⟩]
  check "access-only alias carried-store whole output" aliasResult.ret (aliasExpected, some 0)
  check "alias branch five events" aliasResult.time 5

#eval runCases []

end Cslib.Algorithms.Lean.DoublyLinkedList.PrependTests

end
