/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Specs.InsertionSort
import CSLibExt.Specs.SelectionSort
-- Executable #eval clients need the algorithms in the interpreter phase.
meta import CSLibExt.Specs.InsertionSort
meta import CSLibExt.Specs.SelectionSort

open CSLibExt.Specs.Sorting
open Cslib.Algorithms.Lean.TimeM (insertionSort selectionSort)

universe u

-- Public clients retain the Nat call syntax and can use any linear order.
example (xs : List Nat) : SortingSpec xs (isort xs) := sorting_isort xs

example {α : Type u} [LinearOrder α] (xs : List α) :
    SortingSpec xs (isort xs) := sorting_isort xs

example {α : Type u} [LinearOrder α] (xs : List α) :
    SortingSpec xs (insertionSort xs).ret := sorting_insertionSort xs

example {α : Type u} [LinearOrder α] (xs : List α) :
    SortingSpec xs (selectionSort xs).ret := sorting_selectionSort xs

example (xs : List (ULift.{1} Int)) :
    SortingSpec xs (insertionSort xs).ret := sorting_insertionSort xs

example (xs : List (ULift.{1} Int)) :
    SortingSpec xs (selectionSort xs).ret := sorting_selectionSort xs

example (x : Int) (xs : List Int) :
    CSLibExt.Specs.Sorting.insert x xs = List.orderedInsert (· ≤ ·) x xs := rfl

example (xs : List Int) : isort xs = List.insertionSort (· ≤ ·) xs := rfl

example (xs : List Int) : (insertionSort xs).ret = isort xs :=
  Cslib.Algorithms.Lean.TimeM.ret_insertionSort xs

-- Former insertion helper clients use the canonical Mathlib API directly.
example {x z : Nat} {xs : List Nat}
    (h : z ∈ CSLibExt.Specs.Sorting.insert x xs) :
    z = x ∨ z ∈ xs := List.mem_orderedInsert (· ≤ ·) |>.mp h

example (x : Nat) (xs : List Nat) :
    (CSLibExt.Specs.Sorting.insert x xs).Perm (x :: xs) :=
  List.perm_orderedInsert (· ≤ ·) x xs

example {x : Nat} {xs : List Nat} (h : SortedProp xs) :
    SortedProp (CSLibExt.Specs.Sorting.insert x xs) := h.orderedInsert x xs

-- Kernel-checked independent expected results for both implementations.
example : isort ([2, -1, 2, 0] : List Int) = [-1, 0, 2, 2] := by
  simp [isort, List.insertionSort_cons, List.orderedInsert_cons]

example : (insertionSort ([2, -1, 2, 0] : List Int)).ret =
    [-1, 0, 2, 2] := rfl

example : (selectionSort ([2, -1, 2, 0] : List Int)).ret =
    [-1, 0, 2, 2] := rfl

private def satisfies (xs ys : List Int) : Bool :=
  @decide (SortingSpec xs ys)
    (inferInstanceAs (Decidable (ys.Perm xs ∧ ys.Pairwise (· ≤ ·))))

private def checkCase (xs expected : List Int) : IO Unit := do
  let results := [("Mathlib", isort xs),
    ("TimeM insertion", (insertionSort xs).ret),
    ("TimeM selection", (selectionSort xs).ret)]
  for (name, result) in results do
    unless result == expected do
      throw <| IO.userError s!"{name}: {xs} => {result}, expected {expected}"
    unless satisfies xs result do
      throw <| IO.userError s!"{name}: violated SortingSpec on {xs}"

#eval do
  let cases : List (String × List Int × List Int) :=
    [("empty", [], []), ("singleton", [-1], [-1]),
      ("sorted", [-2, -1, 0, 1, 2], [-2, -1, 0, 1, 2]),
      ("reverse", [2, 1, 0, -1, -2], [-2, -1, 0, 1, 2]),
      ("duplicates", [2, -1, 2, 0, -1, 2], [-1, -1, 0, 2, 2, 2]),
      ("all equal", [1, 1, 1, 1], [1, 1, 1, 1]),
      ("mixed signs", [2, -1, 2, 0], [-1, 0, 2, 2])]
  for (name, xs, expected) in cases do
    checkCase xs expected
    IO.println s!"{name}: {xs} => {expected} (3 implementations)"
  unless !satisfies [1, 2] [2, 1] && !satisfies [1, 1, 2] [1, 2] do
    throw <| IO.userError "SortingSpec accepted an invalid witness"

-- Enumerate input words, not an alternative sorting implementation.
private def words (length : Nat) : List (List Int) :=
  match length with
  | 0 => [[]]
  | n + 1 => [-2, -1, 0, 1, 2].flatMap fun x => (words n).map (x :: ·)

#eval do
  let inputs : List (List Int) := (List.range 6).flatMap words
  unless inputs.length == 3906 && inputs.length > 0 do
    throw <| IO.userError s!"Invalid enumeration: {inputs.length}"
  for xs in inputs do
    -- Independent oracle: output each alphabet value by its input count.
    let expected : List Int := [-2, -1, 0, 1, 2].flatMap fun x =>
      List.replicate (List.count x xs) x
    checkCase xs expected
  IO.println s!"{inputs.length} words, lengths 0..5, alphabet -2..2: passed"

#eval do
  let xs : List (ULift.{1} Int) := [⟨2⟩, ⟨-1⟩, ⟨2⟩, ⟨0⟩]
  for result in [isort xs, (insertionSort xs).ret, (selectionSort xs).ret] do
    unless List.map ULift.down result == ([-1, 0, 2, 2] : List Int) do
      throw <| IO.userError "Higher-universe result mismatch"
  IO.println "ULift.{1} Int: [-1, 0, 2, 2] (3 implementations)"
