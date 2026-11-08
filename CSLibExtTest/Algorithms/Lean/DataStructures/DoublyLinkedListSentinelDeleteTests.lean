/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Sentinel.Delete
public meta import Cslib.Algorithms.Lean.TimeM

/-!
# Executed circular-sentinel deletion fixtures

The ordinary module hook executes all eleven populated cases and 55 assertions.
Selected source-event cost is two for represented deletion and access-valid aliases.
Private wrong-expectation branches are retained for verifier controls only.
-/

@[expose] public meta section

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.DoublyLinkedList

private def check {α : Type} [BEq α] [Repr α]
    (label : String) (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: expected {repr expected}, got {repr actual}"
  IO.println s!"{label}: {repr actual}"

private def case0 (args : List String) : IO Unit := do
  let store0 : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(0, "sentinel"), some 1, some 1⟩,
    some ⟨(-9, "singleton"), some 0, some 0⟩]
  let result0 := sentinelDelete store0 1 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected0 : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(0, "sentinel"), some 0, some 0⟩,
    some ⟨(-9, "singleton"), some 0, some 0⟩]
  check "singleton coalesced sentinel writes full store" result0.ret
    (if args == ["wrong-snapshot"] then store0 else expected0)
  check "singleton coalesced sentinel writes source events" result0.time
    (if args == ["wrong-count"] then 3 else 2)
  check "singleton coalesced sentinel writes selected record retained" (result0.ret.get 1)
    (if args == ["wrong-free"] then none else store0.get 1)
  check "singleton coalesced sentinel writes payloads" (result0.ret.map fun o => o.map Node.payload)
    (if args == ["wrong-payload"] then (store0.set 1
      (some ⟨(99, "wrong"), some 0, some 0⟩)).map (fun o => o.map Node.payload) else
        store0.map fun o => o.map Node.payload)
  check "singleton coalesced sentinel writes allocation domain" (result0.ret.map Option.isSome)
    (store0.map Option.isSome)

private def case1 (_args : List String) : IO Unit := do
  let store1 : Vector (Option (Node (Int × String) (Fin 4))) 4 :=
    #v[some ⟨(0, "sentinel"), some 1, some 3⟩,
    some ⟨(9, "first satellite"), some 2, some 0⟩,
    some ⟨(9, "middle satellite"), some 3, some 1⟩,
    some ⟨(9, "last satellite"), some 0, some 2⟩]
  let result1 := sentinelDelete store1 1 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected1 : Vector (Option (Node (Int × String) (Fin 4))) 4 :=
    #v[some ⟨(0, "sentinel"), some 2, some 3⟩,
    some ⟨(9, "first satellite"), some 2, some 0⟩,
    some ⟨(9, "middle satellite"), some 3, some 0⟩,
    some ⟨(9, "last satellite"), some 0, some 2⟩]
  check "head with duplicate keys and satellites full store" result1.ret
    (expected1)
  check "head with duplicate keys and satellites source events" result1.time
    (2)
  check "head with duplicate keys and satellites selected record retained" (result1.ret.get 1)
    (store1.get 1)
  check "head with duplicate keys and satellites payloads"
    (result1.ret.map fun o => o.map Node.payload)
    (store1.map fun o => o.map Node.payload)
  check "head with duplicate keys and satellites allocation domain" (result1.ret.map Option.isSome)
    (store1.map Option.isSome)

private def case2 (_args : List String) : IO Unit := do
  let store2 : Vector (Option (Node (Int × String) (Fin 4))) 4 :=
    #v[some ⟨(0, "sentinel"), some 1, some 3⟩,
    some ⟨(9, "first satellite"), some 2, some 0⟩,
    some ⟨(9, "middle satellite"), some 3, some 1⟩,
    some ⟨(9, "last satellite"), some 0, some 2⟩]
  let result2 := sentinelDelete store2 2 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected2 : Vector (Option (Node (Int × String) (Fin 4))) 4 :=
    #v[some ⟨(0, "sentinel"), some 1, some 3⟩,
    some ⟨(9, "first satellite"), some 3, some 0⟩,
    some ⟨(9, "middle satellite"), some 3, some 1⟩,
    some ⟨(9, "last satellite"), some 0, some 1⟩]
  check "interior with duplicate keys and satellites full store" result2.ret
    (expected2)
  check "interior with duplicate keys and satellites source events" result2.time
    (2)
  check "interior with duplicate keys and satellites selected record retained" (result2.ret.get 2)
    (store2.get 2)
  check "interior with duplicate keys and satellites payloads"
    (result2.ret.map fun o => o.map Node.payload)
    (store2.map fun o => o.map Node.payload)
  check "interior with duplicate keys and satellites allocation domain"
    (result2.ret.map Option.isSome)
    (store2.map Option.isSome)

private def case3 (_args : List String) : IO Unit := do
  let store3 : Vector (Option (Node (Int × String) (Fin 4))) 4 :=
    #v[some ⟨(0, "sentinel"), some 1, some 3⟩,
    some ⟨(9, "first satellite"), some 2, some 0⟩,
    some ⟨(9, "middle satellite"), some 3, some 1⟩,
    some ⟨(9, "last satellite"), some 0, some 2⟩]
  let result3 := sentinelDelete store3 3 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected3 : Vector (Option (Node (Int × String) (Fin 4))) 4 :=
    #v[some ⟨(0, "sentinel"), some 1, some 2⟩,
    some ⟨(9, "first satellite"), some 2, some 0⟩,
    some ⟨(9, "middle satellite"), some 0, some 1⟩,
    some ⟨(9, "last satellite"), some 0, some 2⟩]
  check "tail with duplicate keys and satellites full store" result3.ret
    (expected3)
  check "tail with duplicate keys and satellites source events" result3.time
    (2)
  check "tail with duplicate keys and satellites selected record retained" (result3.ret.get 3)
    (store3.get 3)
  check "tail with duplicate keys and satellites payloads"
    (result3.ret.map fun o => o.map Node.payload)
    (store3.map fun o => o.map Node.payload)
  check "tail with duplicate keys and satellites allocation domain" (result3.ret.map Option.isSome)
    (store3.map Option.isSome)

private def case4 (_args : List String) : IO Unit := do
  let store4 : Vector (Option (Node (Int × String) (Fin 8))) 8 :=
    #v[some ⟨(0, "first sentinel"), some 1, some 2⟩,
    some ⟨(9, "first circle head"), some 2, some 0⟩,
    some ⟨(9, "first circle tail"), some 0, some 1⟩,
    some ⟨(0, "second sentinel"), some 4, some 5⟩,
    some ⟨(9, "second circle head"), some 5, some 3⟩,
    some ⟨(9, "second circle tail"), some 3, some 4⟩,
    none,
    some ⟨(-3, "detached"), some 7, some 7⟩]
  let result4 := sentinelDelete store4 1 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected4 : Vector (Option (Node (Int × String) (Fin 8))) 8 :=
    #v[some ⟨(0, "first sentinel"), some 2, some 2⟩,
    some ⟨(9, "first circle head"), some 2, some 0⟩,
    some ⟨(9, "first circle tail"), some 0, some 0⟩,
    some ⟨(0, "second sentinel"), some 4, some 5⟩,
    some ⟨(9, "second circle head"), some 5, some 3⟩,
    some ⟨(9, "second circle tail"), some 3, some 4⟩,
    none,
    some ⟨(-3, "detached"), some 7, some 7⟩]
  check "two circles head absent detached full store" result4.ret
    (expected4)
  check "two circles head absent detached source events" result4.time
    (2)
  check "two circles head absent detached selected record retained" (result4.ret.get 1)
    (store4.get 1)
  check "two circles head absent detached payloads" (result4.ret.map fun o => o.map Node.payload)
    (store4.map fun o => o.map Node.payload)
  check "two circles head absent detached allocation domain" (result4.ret.map Option.isSome)
    (store4.map Option.isSome)

private def case5 (_args : List String) : IO Unit := do
  let store5 : Vector (Option (Node (Int × String) (Fin 8))) 8 :=
    #v[some ⟨(0, "first sentinel"), some 1, some 2⟩,
    some ⟨(9, "first circle head"), some 2, some 0⟩,
    some ⟨(9, "first circle tail"), some 0, some 1⟩,
    some ⟨(0, "second sentinel"), some 4, some 5⟩,
    some ⟨(9, "second circle head"), some 5, some 3⟩,
    some ⟨(9, "second circle tail"), some 3, some 4⟩,
    none,
    some ⟨(-3, "detached"), some 7, some 7⟩]
  let result5 := sentinelDelete store5 2 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected5 : Vector (Option (Node (Int × String) (Fin 8))) 8 :=
    #v[some ⟨(0, "first sentinel"), some 1, some 1⟩,
    some ⟨(9, "first circle head"), some 0, some 0⟩,
    some ⟨(9, "first circle tail"), some 0, some 1⟩,
    some ⟨(0, "second sentinel"), some 4, some 5⟩,
    some ⟨(9, "second circle head"), some 5, some 3⟩,
    some ⟨(9, "second circle tail"), some 3, some 4⟩,
    none,
    some ⟨(-3, "detached"), some 7, some 7⟩]
  check "two circles tail absent detached full store" result5.ret
    (expected5)
  check "two circles tail absent detached source events" result5.time
    (2)
  check "two circles tail absent detached selected record retained" (result5.ret.get 2)
    (store5.get 2)
  check "two circles tail absent detached payloads" (result5.ret.map fun o => o.map Node.payload)
    (store5.map fun o => o.map Node.payload)
  check "two circles tail absent detached allocation domain" (result5.ret.map Option.isSome)
    (store5.map Option.isSome)

private def case6 (_args : List String) : IO Unit := do
  let store6 : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(9, "selected"), some 1, some 1⟩,
    some ⟨(25, "same neighbour"), none, none⟩]
  let result6 := sentinelDelete store6 0 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected6 : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(9, "selected"), some 1, some 1⟩,
    some ⟨(25, "same neighbour"), some 1, some 1⟩]
  check "access valid equal neighbours without representation full store" result6.ret
    (expected6)
  check "access valid equal neighbours without representation source events" result6.time
    (2)
  check "access valid equal neighbours without representation selected record retained"
    (result6.ret.get 0)
    (store6.get 0)
  check "access valid equal neighbours without representation payloads"
    (result6.ret.map fun o => o.map Node.payload)
    (store6.map fun o => o.map Node.payload)
  check "access valid equal neighbours without representation allocation domain"
    (result6.ret.map Option.isSome)
    (store6.map Option.isSome)

private def case7 (_args : List String) : IO Unit := do
  let store7 : Vector (Option (Node (Int × String) (Fin 1))) 1 :=
    #v[some ⟨(-9, "self"), some 0, some 0⟩]
  let result7 := sentinelDelete store7 0 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected7 : Vector (Option (Node (Int × String) (Fin 1))) 1 :=
    #v[some ⟨(-9, "self"), some 0, some 0⟩]
  check "access valid self selected full store" result7.ret
    (expected7)
  check "access valid self selected source events" result7.time
    (2)
  check "access valid self selected selected record retained" (result7.ret.get 0)
    (store7.get 0)
  check "access valid self selected payloads" (result7.ret.map fun o => o.map Node.payload)
    (store7.map fun o => o.map Node.payload)
  check "access valid self selected allocation domain" (result7.ret.map Option.isSome)
    (store7.map Option.isSome)

private def case8 (_args : List String) : IO Unit := do
  let store8 : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(9, "selected"), some 1, some 0⟩,
    some ⟨(25, "next"), some 1, some 0⟩]
  let result8 := sentinelDelete store8 0 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected8 : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(9, "selected"), some 1, some 0⟩,
    some ⟨(25, "next"), some 1, some 0⟩]
  check "access valid predecessor equals selected full store" result8.ret
    (expected8)
  check "access valid predecessor equals selected source events" result8.time
    (2)
  check "access valid predecessor equals selected selected record retained" (result8.ret.get 0)
    (store8.get 0)
  check "access valid predecessor equals selected payloads"
    (result8.ret.map fun o => o.map Node.payload)
    (store8.map fun o => o.map Node.payload)
  check "access valid predecessor equals selected allocation domain" (result8.ret.map Option.isSome)
    (store8.map Option.isSome)

private def case9 (_args : List String) : IO Unit := do
  let store9 : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(9, "selected"), some 0, some 1⟩,
    some ⟨(25, "prev"), some 0, some 1⟩]
  let result9 := sentinelDelete store9 0 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected9 : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
    #v[some ⟨(9, "selected"), some 0, some 1⟩,
    some ⟨(25, "prev"), some 0, some 1⟩]
  check "access valid successor equals selected full store" result9.ret
    (expected9)
  check "access valid successor equals selected source events" result9.time
    (2)
  check "access valid successor equals selected selected record retained" (result9.ret.get 0)
    (store9.get 0)
  check "access valid successor equals selected payloads"
    (result9.ret.map fun o => o.map Node.payload)
    (store9.map fun o => o.map Node.payload)
  check "access valid successor equals selected allocation domain" (result9.ret.map Option.isSome)
    (store9.map Option.isSome)

private def case10 (_args : List String) : IO Unit := do
  let store10 : Vector (Option (Node (Int × String) (Fin 3))) 3 :=
    #v[some ⟨(0, "empty sentinel"), some 0, some 0⟩,
    some ⟨(9, "detached selected"), some 1, some 1⟩,
    none]
  let result10 := sentinelDelete store10 1 (by rfl) (by rfl) (by rfl)
    (by intro p he; cases Option.some.inj he; rfl)
    (by intro n he; cases Option.some.inj he; rfl)
  let expected10 : Vector (Option (Node (Int × String) (Fin 3))) 3 :=
    #v[some ⟨(0, "empty sentinel"), some 0, some 0⟩,
    some ⟨(9, "detached selected"), some 1, some 1⟩,
    none]
  check "empty represented circle separate from deletion full store" result10.ret
    (expected10)
  check "empty represented circle separate from deletion source events" result10.time
    (2)
  check "empty represented circle separate from deletion selected record retained"
    (result10.ret.get 1)
    (store10.get 1)
  check "empty represented circle separate from deletion payloads"
    (result10.ret.map fun o => o.map Node.payload)
    (store10.map fun o => o.map Node.payload)
  check "empty represented circle separate from deletion allocation domain"
    (result10.ret.map Option.isSome)
    (store10.map Option.isSome)

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

#eval runCases []

end
