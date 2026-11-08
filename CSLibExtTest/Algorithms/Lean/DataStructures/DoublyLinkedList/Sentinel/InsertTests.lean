/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Sentinel.Insert
public meta import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Basic
public meta import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Int.Basic

/-!
# Executed LIST-INSERT-prime fixtures

The ordinary hook executes all12 cases, checking complete carried stores, writes,
allocation and payloads. Seven represented fixtures also check every circular
link before/after, including a genuine second disjoint circle and absent cells.
Five additional access-valid alias/noncircle cases exercise the general executor.
Private wrong-expectation modes are assertion controls, not alternative execution.
-/

@[expose] public meta section
open Cslib.Algorithms.Lean.DoublyLinkedList

private def check {α : Type} [BEq α] [Repr α]
    (label : String) (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: expected {repr expected}, got {repr actual}"
  IO.println s!"{label}: {repr actual}"

private def checkCircle {α : Type} {n : Nat}
    (label : String) (store : Vector (Option (Node α (Fin n))) n)
    (s : Fin n) (ids : List (Fin n)) : IO Unit := do
  check (label ++ " nodup") (decide ids.Nodup) true
  check (label ++ " sentinel excluded") (decide (s ∉ ids)) true
  check (label ++ " sentinel links")
    ((store.get s).map fun node => (node.next, node.prev))
    (some (some (ids.headD s), some (ids.getLastD s)))
  for i in [:ids.length] do
    check (label ++ " data links " ++ toString i)
      ((store.get (ids[i]?.getD s)).map fun node => (node.next, node.prev))
      (some (some (ids[i + 1]?.getD s), some (if i = 0 then s else ids[i - 1]?.getD s)))

private def case0 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(0, "sentinel"), some 0, some 0⟩,
    some ⟨(9, "new"), some 1, none⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(0, "sentinel"), some 1, some 1⟩,
    some ⟨(9, "new"), some 0, some 0⟩]
  let result := sentinelInsert store 1 0 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "empty carried sentinel full store" result.ret
    (if args == ["wrong-snapshot"] && 0 == 0 then store else expected)
  check "empty carried sentinel writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "empty carried sentinel domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 1 none).map Option.isSome else store.map Option.isSome)
  check "empty carried sentinel payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 1 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)
  checkCircle "empty carried sentinel circle input 0" store 0 []
  checkCircle "empty carried sentinel circle output 0" result.ret 0 [1]

private def case1 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 5))) 5 :=
    #v[some ⟨(0, "sentinel-0"), some 1, some 3⟩,
    some ⟨(9, "satellite-1"), some 2, some 0⟩,
    some ⟨(9, "satellite-2"), some 3, some 1⟩,
    some ⟨(9, "satellite-3"), some 0, some 2⟩,
    some ⟨(9, "fresh duplicate key"), some 4, some 4⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 5))) 5 :=
    #v[some ⟨(0, "sentinel-0"), some 4, some 3⟩,
    some ⟨(9, "satellite-1"), some 2, some 4⟩,
    some ⟨(9, "satellite-2"), some 3, some 1⟩,
    some ⟨(9, "satellite-3"), some 0, some 2⟩,
    some ⟨(9, "fresh duplicate key"), some 1, some 0⟩]
  let result := sentinelInsert store 4 0 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "prepend duplicate keys full store" result.ret
    (if args == ["wrong-snapshot"] && 1 == 0 then store else expected)
  check "prepend duplicate keys writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "prepend duplicate keys domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 4 none).map Option.isSome else store.map Option.isSome)
  check "prepend duplicate keys payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 4 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)
  checkCircle "prepend duplicate keys circle input 0" store 0 [1,2,3]
  checkCircle "prepend duplicate keys circle output 0" result.ret 0 [4,1,2,3]

private def case2 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 5))) 5 :=
    #v[some ⟨(0, "sentinel-0"), some 1, some 3⟩,
    some ⟨(9, "satellite-1"), some 2, some 0⟩,
    some ⟨(9, "satellite-2"), some 3, some 1⟩,
    some ⟨(9, "satellite-3"), some 0, some 2⟩,
    some ⟨(9, "fresh duplicate key"), some 4, some 4⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 5))) 5 :=
    #v[some ⟨(0, "sentinel-0"), some 1, some 4⟩,
    some ⟨(9, "satellite-1"), some 2, some 0⟩,
    some ⟨(9, "satellite-2"), some 3, some 1⟩,
    some ⟨(9, "satellite-3"), some 4, some 2⟩,
    some ⟨(9, "fresh duplicate key"), some 0, some 3⟩]
  let result := sentinelInsert store 4 3 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "append duplicate keys full store" result.ret
    (if args == ["wrong-snapshot"] && 2 == 0 then store else expected)
  check "append duplicate keys writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "append duplicate keys domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 4 none).map Option.isSome else store.map Option.isSome)
  check "append duplicate keys payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 4 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)
  checkCircle "append duplicate keys circle input 0" store 0 [1,2,3]
  checkCircle "append duplicate keys circle output 0" result.ret 0 [1,2,3,4]

private def case3 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 5))) 5 :=
    #v[some ⟨(0, "sentinel-0"), some 1, some 3⟩,
    some ⟨(9, "satellite-1"), some 2, some 0⟩,
    some ⟨(9, "satellite-2"), some 3, some 1⟩,
    some ⟨(9, "satellite-3"), some 0, some 2⟩,
    some ⟨(9, "fresh duplicate key"), some 4, some 4⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 5))) 5 :=
    #v[some ⟨(0, "sentinel-0"), some 1, some 3⟩,
    some ⟨(9, "satellite-1"), some 2, some 0⟩,
    some ⟨(9, "satellite-2"), some 4, some 1⟩,
    some ⟨(9, "satellite-3"), some 0, some 4⟩,
    some ⟨(9, "fresh duplicate key"), some 3, some 2⟩]
  let result := sentinelInsert store 4 2 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "interior duplicate keys full store" result.ret
    (if args == ["wrong-snapshot"] && 3 == 0 then store else expected)
  check "interior duplicate keys writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "interior duplicate keys domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 4 none).map Option.isSome else store.map Option.isSome)
  check "interior duplicate keys payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 4 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)
  checkCircle "interior duplicate keys circle input 0" store 0 [1,2,3]
  checkCircle "interior duplicate keys circle output 0" result.ret 0 [1,2,4,3]

private def case4 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 9))) 9 :=
    #v[some ⟨(0, "sentinel-0"), some 1, some 2⟩,
    some ⟨(9, "satellite-1"), some 2, some 0⟩,
    some ⟨(9, "satellite-2"), some 0, some 1⟩,
    some ⟨(0, "sentinel-3"), some 4, some 5⟩,
    some ⟨(9, "satellite-4"), some 5, some 3⟩,
    some ⟨(9, "satellite-5"), some 3, some 4⟩,
    none,
    some ⟨(-3, "fresh payload"), some 7, some 7⟩,
    some ⟨(-7, "detached frame"), some 8, some 8⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 9))) 9 :=
    #v[some ⟨(0, "sentinel-0"), some 7, some 2⟩,
    some ⟨(9, "satellite-1"), some 2, some 7⟩,
    some ⟨(9, "satellite-2"), some 0, some 1⟩,
    some ⟨(0, "sentinel-3"), some 4, some 5⟩,
    some ⟨(9, "satellite-4"), some 5, some 3⟩,
    some ⟨(9, "satellite-5"), some 3, some 4⟩,
    none,
    some ⟨(-3, "fresh payload"), some 1, some 0⟩,
    some ⟨(-7, "detached frame"), some 8, some 8⟩]
  let result := sentinelInsert store 7 0 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "prepend two disjoint circles absent detached full store" result.ret
    (if args == ["wrong-snapshot"] && 4 == 0 then store else expected)
  check "prepend two disjoint circles absent detached writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "prepend two disjoint circles absent detached domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 7 none).map Option.isSome else store.map Option.isSome)
  check "prepend two disjoint circles absent detached payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 7 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)
  checkCircle "prepend two disjoint circles absent detached circle input 0" store 0 [1,2]
  checkCircle "prepend two disjoint circles absent detached circle output 0" result.ret 0 [7,1,2]
  checkCircle "prepend two disjoint circles absent detached circle input 3" store 3 [4,5]
  checkCircle "prepend two disjoint circles absent detached circle output 3" result.ret 3 [4,5]

private def case5 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 9))) 9 :=
    #v[some ⟨(0, "sentinel-0"), some 1, some 2⟩,
    some ⟨(9, "satellite-1"), some 2, some 0⟩,
    some ⟨(9, "satellite-2"), some 0, some 1⟩,
    some ⟨(0, "sentinel-3"), some 4, some 5⟩,
    some ⟨(9, "satellite-4"), some 5, some 3⟩,
    some ⟨(9, "satellite-5"), some 3, some 4⟩,
    none,
    some ⟨(-3, "fresh payload"), some 7, some 7⟩,
    some ⟨(-7, "detached frame"), some 8, some 8⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 9))) 9 :=
    #v[some ⟨(0, "sentinel-0"), some 1, some 7⟩,
    some ⟨(9, "satellite-1"), some 2, some 0⟩,
    some ⟨(9, "satellite-2"), some 7, some 1⟩,
    some ⟨(0, "sentinel-3"), some 4, some 5⟩,
    some ⟨(9, "satellite-4"), some 5, some 3⟩,
    some ⟨(9, "satellite-5"), some 3, some 4⟩,
    none,
    some ⟨(-3, "fresh payload"), some 0, some 2⟩,
    some ⟨(-7, "detached frame"), some 8, some 8⟩]
  let result := sentinelInsert store 7 2 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "append two disjoint circles absent detached full store" result.ret
    (if args == ["wrong-snapshot"] && 5 == 0 then store else expected)
  check "append two disjoint circles absent detached writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "append two disjoint circles absent detached domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 7 none).map Option.isSome else store.map Option.isSome)
  check "append two disjoint circles absent detached payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 7 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)
  checkCircle "append two disjoint circles absent detached circle input 0" store 0 [1,2]
  checkCircle "append two disjoint circles absent detached circle output 0" result.ret 0 [1,2,7]
  checkCircle "append two disjoint circles absent detached circle input 3" store 3 [4,5]
  checkCircle "append two disjoint circles absent detached circle output 3" result.ret 3 [4,5]

private def case6 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 7))) 7 :=
    #v[some ⟨(0, "sentinel-0"), some 0, some 0⟩,
    some ⟨(0, "sentinel-1"), some 2, some 3⟩,
    some ⟨(9, "satellite-2"), some 3, some 1⟩,
    some ⟨(9, "satellite-3"), some 1, some 2⟩,
    none,
    some ⟨(-5, "fresh empty"), none, none⟩,
    some ⟨(9, "detached"), some 6, some 6⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 7))) 7 :=
    #v[some ⟨(0, "sentinel-0"), some 5, some 5⟩,
    some ⟨(0, "sentinel-1"), some 2, some 3⟩,
    some ⟨(9, "satellite-2"), some 3, some 1⟩,
    some ⟨(9, "satellite-3"), some 1, some 2⟩,
    none,
    some ⟨(-5, "fresh empty"), some 0, some 0⟩,
    some ⟨(9, "detached"), some 6, some 6⟩]
  let result := sentinelInsert store 5 0 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "empty with second disjoint circle and absent cell full store" result.ret
    (if args == ["wrong-snapshot"] && 6 == 0 then store else expected)
  check "empty with second disjoint circle and absent cell writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "empty with second disjoint circle and absent cell domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 5 none).map Option.isSome else store.map Option.isSome)
  check "empty with second disjoint circle and absent cell payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 5 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)
  checkCircle "empty with second disjoint circle and absent cell circle input 0" store 0 []
  checkCircle "empty with second disjoint circle and absent cell circle output 0" result.ret 0 [5]
  checkCircle "empty with second disjoint circle and absent cell circle input 1" store 1 [2,3]
  checkCircle "empty with second disjoint circle and absent cell circle output 1" result.ret 1 [2,3]

private def case7 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(-1, "xy"), some 1, some 0⟩,
    some ⟨(9, "successor"), none, none⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(-1, "xy"), some 0, some 0⟩,
    some ⟨(9, "successor"), none, some 0⟩]
  let result := sentinelInsert store 0 0 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "alias x equals y full store" result.ret
    (if args == ["wrong-snapshot"] && 7 == 0 then store else expected)
  check "alias x equals y writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "alias x equals y domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 0 none).map Option.isSome else store.map Option.isSome)
  check "alias x equals y payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 0 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)

private def case8 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(9, "y"), some 1, some 0⟩,
    some ⟨(-1, "xz"), none, none⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(9, "y"), some 1, some 0⟩,
    some ⟨(-1, "xz"), some 1, some 1⟩]
  let result := sentinelInsert store 1 0 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "alias x equals successor full store" result.ret
    (if args == ["wrong-snapshot"] && 8 == 0 then store else expected)
  check "alias x equals successor writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "alias x equals successor domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 1 none).map Option.isSome else store.map Option.isSome)
  check "alias x equals successor payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 1 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)

private def case9 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(9, "yz"), some 0, some 0⟩,
    some ⟨(-1, "x"), none, none⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(9, "yz"), some 1, some 1⟩,
    some ⟨(-1, "x"), some 0, some 0⟩]
  let result := sentinelInsert store 1 0 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "alias y equals successor full store" result.ret
    (if args == ["wrong-snapshot"] && 9 == 0 then store else expected)
  check "alias y equals successor writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "alias y equals successor domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 1 none).map Option.isSome else store.map Option.isSome)
  check "alias y equals successor payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 1 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)

private def case10 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 1))) 1 :=
    #v[some ⟨(-9, "self"), some 0, some 0⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 1))) 1 :=
    #v[some ⟨(-9, "self"), some 0, some 0⟩]
  let result := sentinelInsert store 0 0 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "all targets coincide full store" result.ret
    (if args == ["wrong-snapshot"] && 10 == 0 then store else expected)
  check "all targets coincide writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "all targets coincide domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 0 none).map Option.isSome else store.map Option.isSome)
  check "all targets coincide payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 0 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)

private def case11 (args : List String) : IO Unit := do
  let store : Vector (Option (Node (Int × String) (Fin 3))) 3 :=
    #v[some ⟨(1, "y"), some 1, none⟩,
    some ⟨(2, "z"), none, none⟩,
    some ⟨(3, "x"), none, none⟩]
  let expected : Vector (Option (Node (Int × String) (Fin 3))) 3 :=
    #v[some ⟨(1, "y"), some 2, none⟩,
    some ⟨(2, "z"), none, some 2⟩,
    some ⟨(3, "x"), some 1, some 0⟩]
  let result := sentinelInsert store 2 0 (by rfl) (by rfl) (by rfl)
    (by intro z he; cases Option.some.inj he; rfl)
  check "distinct access-valid noncircle full store" result.ret
    (if args == ["wrong-snapshot"] && 11 == 0 then store else expected)
  check "distinct access-valid noncircle writes" result.time (if args == ["wrong-count"] then 5 else 4)
  check "distinct access-valid noncircle domain" (result.ret.map Option.isSome)
    (if args == ["wrong-domain"] then (store.set 2 none).map Option.isSome else store.map Option.isSome)
  check "distinct access-valid noncircle payloads" (result.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store.set 2 none).map (fun o => o.map Node.payload)
      else store.map fun o => o.map Node.payload)

private def runCases (args : List String) : IO Unit := do
  case0 args
  case1 args
  case2 args
  case3 args
  case4 args
  case5 args
  case6 args
  case7 args
  case8 args
  case9 args
  case10 args
  case11 args
  IO.println "ACTUAL_SENTINEL_INSERT_CASES 12"

#eval runCases []
