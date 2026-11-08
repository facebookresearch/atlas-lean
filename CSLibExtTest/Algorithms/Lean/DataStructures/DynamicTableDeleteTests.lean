/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.DynamicTable.Delete

/-! Runtime assertions for dynamic-table deletion and lookup: whole saved slots,
item counts, contents, and logical-position lookups. -/

@[expose] public meta section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DynamicTable.DeleteTests

universe u

private def check {α : Type u} [DecidableEq α] [Repr α]
    (label : String) (actual expected : α) : IO Unit := do
  if actual ≠ expected then
    throw <| IO.userError s!"{label}: expected {repr expected}, actual {repr actual}"
  IO.println s!"{label}: {repr actual}"

private def checkTable {α : Type u} [DecidableEq α] [Repr α]
    (label : String) (actual : Table α)
    (slots : Array (Option α)) (num : Nat) : IO Unit := do
  check (label ++ " whole slots/num") (actual.slots, actual.num) (slots, num)

private def runCases (_args : List String) : IO Unit := do
  -- Empty deletion: unallocated and allocated empty tables.
  checkTable "delete unallocated empty" (tableDelete (empty : Table Nat)) #[] 0
  check "empty contents" (contents (empty : Table Nat)) (#[] : Array Nat)
  check "empty lookup" (get? (empty : Table Nat) 0) (none : Option Nat)
  check "empty delete lookup" (get? (tableDelete (empty : Table Nat)) 0)
    (none : Option Nat)
  let allocatedEmpty : Table Nat := ⟨#[none, none, none, none], 0, by decide⟩
  checkTable "delete allocated empty keeps capacity" (tableDelete allocatedEmpty)
    #[none, none, none, none] 0
  check "allocated empty lookup" (get? allocatedEmpty 0) (none : Option Nat)
  -- Singleton capacity boundaries.
  let singletonOne : Table Nat := ⟨#[some 7], 1, by decide⟩
  check "singleton lookup" (get? singletonOne 0) (some 7)
  checkTable "delete singleton capacity1 contracts to zero"
    (tableDelete singletonOne) #[] 0
  check "deleted singleton lookup" (get? (tableDelete singletonOne) 0)
    (none : Option Nat)
  let singletonSpare : Table Nat := ⟨#[some 7, none, none, none], 1, by decide⟩
  checkTable "delete singleton capacity4 contracts to two"
    (tableDelete singletonSpare) #[none, none] 0
  -- Exact quarter after deletion (2 of 8): the strict test does not contract.
  let exactQuarter : Table Nat :=
    ⟨#[some 10, some 20, some 30, none, none, none, none, none], 3, by decide⟩
  checkTable "exact quarter does not contract" (tableDelete exactQuarter)
    #[some 10, some 20, none, none, none, none, none, none] 2
  check "exact quarter contents" (contents (tableDelete exactQuarter)) #[10, 20]
  check "exact quarter retained lookup" (get? (tableDelete exactQuarter) 1)
    (some 20)
  check "exact quarter deleted lookup" (get? (tableDelete exactQuarter) 2)
    (none : Option Nat)
  -- Below quarter after deletion (1 of 8): contracts to half capacity.
  let belowQuarter : Table Nat :=
    ⟨#[some 10, some 20, none, none, none, none, none, none], 2, by decide⟩
  checkTable "below quarter contracts to half" (tableDelete belowQuarter)
    #[some 10, none, none, none] 1
  check "below quarter contents" (contents (tableDelete belowQuarter)) #[10]
  check "below quarter retained lookup" (get? (tableDelete belowQuarter) 0)
    (some 10)
  check "below quarter deleted lookup" (get? (tableDelete belowQuarter) 1)
    (none : Option Nat)
  -- Full table: in-place clearing, retained order.
  let full : Table Nat := ⟨#[some 10, some 20, some 30, some 40], 4, by decide⟩
  checkTable "full table clears last slot in place" (tableDelete full)
    #[some 10, some 20, some 30, none] 3
  check "full contents order" (contents (tableDelete full)) #[10, 20, 30]
  check "full retained lookup first" (get? (tableDelete full) 0) (some 10)
  check "full retained lookup last" (get? (tableDelete full) 2) (some 30)
  check "full deleted lookup" (get? (tableDelete full) 3) (none : Option Nat)
  check "lookup at num" (get? full 4) (none : Option Nat)
  check "lookup far beyond num" (get? full 100) (none : Option Nat)
  -- Repeated deletion passes the exact-quarter point before contracting.
  let chain : Table Nat :=
    ⟨#[some 10, some 20, some 30, some 40, none, none, none, none], 4, by decide⟩
  check "chain one delete size" (tableDelete chain).slots.size 8
  check "chain one delete contents" (contents (tableDelete chain)) #[10, 20, 30]
  check "chain two deletes size (exact quarter)"
    (tableDelete (tableDelete chain)).slots.size 8
  check "chain two deletes contents" (contents (tableDelete (tableDelete chain)))
    #[10, 20]
  check "chain three deletes size (below quarter)"
    (tableDelete (tableDelete (tableDelete chain))).slots.size 4
  check "chain three deletes contents"
    (contents (tableDelete (tableDelete (tableDelete chain)))) #[10]
  check "chain four deletes num"
    (tableDelete (tableDelete (tableDelete (tableDelete chain)))).num 0
  check "chain four deletes contents"
    (contents (tableDelete (tableDelete (tableDelete (tableDelete chain)))))
    (#[] : Array Nat)
  -- Nested `Option` payloads: a stored `none` reads back as `some none`.
  let nested : Table (Option Nat) :=
    ⟨#[some none, some (some 7), some none, none], 3, by decide⟩
  check "nested contents" (contents nested) #[none, some 7, none]
  check "nested stored-none lookup" (get? nested 0) (some none : Option (Option Nat))
  check "nested stored-some lookup" (get? nested 1)
    (some (some 7) : Option (Option Nat))
  check "nested second stored-none lookup" (get? nested 2)
    (some none : Option (Option Nat))
  check "nested absent lookup" (get? nested 3) (none : Option (Option Nat))
  checkTable "nested delete clears last slot" (tableDelete nested)
    #[some none, some (some 7), none, none] 2
  check "nested delete contents" (contents (tableDelete nested)) #[none, some 7]
  check "nested delete retains stored none" (get? (tableDelete nested) 0)
    (some none : Option (Option Nat))
  check "nested deleted position is absent" (get? (tableDelete nested) 2)
    (none : Option (Option Nat))
  let nestedSingleton : Table (Option Nat) := ⟨#[some none], 1, by decide⟩
  check "nested singleton lookup" (get? nestedSingleton 0)
    (some none : Option (Option Nat))
  checkTable "nested singleton delete contracts to zero"
    (tableDelete nestedSingleton) #[] 0
  check "nested singleton deleted lookup" (get? (tableDelete nestedSingleton) 0)
    (none : Option (Option Nat))

#eval runCases []

end Cslib.Algorithms.Lean.DynamicTable.DeleteTests

end
