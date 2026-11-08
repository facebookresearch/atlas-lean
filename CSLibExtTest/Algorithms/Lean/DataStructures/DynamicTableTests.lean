/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.DynamicTable.Basic
public meta import Cslib.Algorithms.Lean.TimeM

/-! Complete saved-slot and selected copy/write event runtime assertions. -/

@[expose] public meta section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DynamicTable.Tests

universe u

private def check {α : Type u} [DecidableEq α] [Repr α]
    (label : String) (actual expected : α) : IO Unit := do
  if actual ≠ expected then
    throw <| IO.userError s!"{label}: expected {repr expected}, actual {repr actual}"
  IO.println s!"{label}: {repr actual}"

private def checkState {α : Type u} [DecidableEq α] [Repr α]
    (label : String) (result : TimeM Nat (Table α))
    (slots : Array (Option α)) (num cost : Nat) : IO Unit := do
  check (label ++ " whole slots/num/cost") (result.ret.slots, result.ret.num, result.time)
    (slots, num, cost)

private structure Payload where
  key : Int
  satellite : String
  deriving DecidableEq, Repr

private def runCases (args : List String) : IO Unit := do
  let full : Table Int := ⟨#[some 10, some (-2), some 10, some 7], 4, by decide⟩
  let result := tableInsert full 3
  let slots : Array (Option Int) :=
    #[some (if args == ["wrong-copy"] then 999 else 10), some (-2), some 10, some 7,
      some 3, none, none, none]
  checkState "full4 doubles saved signed duplicates" result
    (if args == ["wrong-capacity"] then slots.extract 0 4 else slots)
    5 (if args == ["wrong-cost"] then 1 else 5)
  checkState "empty allocates before testing fullness" (tableInsert (empty : Table Int) 9)
    #[some 9] 1 1
  checkState "singleton full1 to2"
    (tableInsert (⟨#[some 7], 1, by decide⟩ : Table Int) (-2)) #[some 7, some (-2)] 2 2
  checkState "full2 to4"
    (tableInsert (⟨#[some (-1), some 4], 2, by decide⟩ : Table Int) (-1))
    #[some (-1), some 4, some (-1), none] 3 3
  checkState "spare3 of4 fills without copying"
    (tableInsert (⟨#[some 1, some 2, some 3, none], 3, by decide⟩ : Table Int) 4)
    #[some 1, some 2, some 3, some 4] 4 1
  let eight : Array (Option Int) := (List.range 8).toArray.map (fun n => some (Int.ofNat n))
  checkState "full8 to16"
    (tableInsert ⟨eight, 8, by
      simp only [eight, Array.size_map, List.size_toArray, List.length_range, Nat.le_refl]⟩ 8)
    ((List.range 9).toArray.map (fun n => some (Int.ofNat n)) ++ Array.replicate 7 none) 9 9
  let sixteen : Array (Option Int) :=
    (List.range 16).toArray.map (fun n => some (Int.ofNat n))
  checkState "full16 to32"
    (tableInsert ⟨sixteen, 16, by
      simp only [sixteen, Array.size_map, List.size_toArray, List.length_range, Nat.le_refl]⟩ 16)
    ((List.range 17).toArray.map (fun n => some (Int.ofNat n)) ++ Array.replicate 15 none)
    17 17
  checkState "arbitrary nonreachable full capacity3 to6"
    (tableInsert (⟨#[some 3, some 3, some (-4)], 3, by decide⟩ : Table Int) 8)
    #[some 3, some 3, some (-4), some 8, none, none] 4 4
  checkState "allocated empty capacity4 does not allocate"
    (tableInsert (⟨#[none, none, none, none], 0, by decide⟩ : Table Int) 4)
    #[some 4, none, none, none] 1 1
  checkState "access-only malformed occupancy still copies every saved cell"
    (tableInsert (⟨#[some 1, none], 2, by decide⟩ : Table Int) 2)
    #[some 1, none, some 2, none] 3 3
  let payloads : Array Int := (List.range 17).toArray.map (fun i => (Int.ofNat (i % 5)) - 2)
  let capacities : Array Nat := #[0, 1, 2, 4, 4, 8, 8, 8, 8, 16, 16, 16, 16, 16, 16, 16, 16, 32]
  let costs : Array Nat := #[0, 1, 3, 6, 7, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31, 48]
  let steps : Array Nat := #[1, 2, 3, 1, 5, 1, 1, 1, 9, 1, 1, 1, 1, 1, 1, 1, 17]
  for i in [:18] do
    let xs := payloads.extract 0 i
    let actual := tableInsertMany empty xs
    let capacity := capacities[i]!
    checkState s!"source prefix{i}" actual
      (xs.map some ++ Array.replicate (capacity - i) none) i costs[i]!
    check s!"source prefix{i} contents and duplicates" (contents actual.ret) xs
    check s!"source prefix{i} occupied/spare cells" (actual.ret.slots.toList.map Option.isSome)
      (List.replicate i true ++ List.replicate (capacity - i) false)
    check s!"source prefix{i} weak aggregate" (decide (actual.time ≤ 3 * i)) true
    if i > 0 then
      check s!"source prefix{i} strict aggregate" (decide (actual.time < 3 * i)) true
      let previous := tableInsertMany empty (payloads.extract 0 (i - 1))
      let next := tableInsert previous.ret payloads[i - 1]!
      check s!"source prefix{i} same-run next write count" next.time steps[i - 1]!
      check s!"source prefix{i} same-run carried slots" next.ret.slots actual.ret.slots
  let first := tableInsert (empty : Table Int) 3
  check "first potential charge is2, not3"
    ((first.time : Int) + 2 * (first.ret.num : Int) - (first.ret.slots.size : Int)) 2
  checkState "strings and repeated empty strings"
    (tableInsertMany empty #["", "same", "same", "\u6f22\u5b57", "tail"])
    #[some "", some "same", some "same", some "\u6f22\u5b57", some "tail", none, none, none] 5 12
  let records : Array Payload := #[⟨7, "first"⟩, ⟨7, "second"⟩, ⟨-2, "third"⟩]
  checkState "arbitrary record satellites survive copies" (tableInsertMany empty records)
    #[some ⟨7, "first"⟩, some ⟨7, "second"⟩, some ⟨-2, "third"⟩, none] 3 6
  checkState "stored none payload differs from unused slot"
    (tableInsertMany empty (#[none, some 7, none] : Array (Option Nat)))
    #[some none, some (some 7), some none, none] 3 6

#eval runCases []

end Cslib.Algorithms.Lean.DynamicTable.Tests

end
