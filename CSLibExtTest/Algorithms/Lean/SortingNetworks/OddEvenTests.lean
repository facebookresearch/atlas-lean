/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.OddEven
public meta import CSLibExt.Algorithms.Lean.SortingNetworks.OddEven
public import Mathlib.Data.Int.Order.Basic
public meta import Mathlib.Data.Int.Order.Basic

/-!
# Odd-even merge sort tests

Executed fixtures: Batcher's odd-even merge sort on `2`, `4`, `8` and `16` wires sorts 200
pseudo-random integer inputs each (output equal to the sorted input), passes `sortsBool` on up
to `8` wires, and has `1, 5, 19, 63` comparators (fewer than the bitonic sorter's `1, 6, 24,
80`), matching `length_oddEvenSorter`; dropping the merger's last layer breaks it. Each run
throws on failure. Closed checks instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.SortingNetworks.OddEven

open Bitonic

private meta def toList {n : ℕ} (v : Fin n → ℤ) : List ℤ := (List.finRange n).map v

private meta def checkSorter (k : ℕ) : IO Unit := do
  let n := 2 ^ k
  let mut s := 17
  for _ in [0:200] do
    let mut xs : List ℤ := []
    for _ in [0:n] do
      s := (s * 1103515245 + 12345) % 2147483648
      xs := xs ++ [((s / 7 % 61 : ℕ) : ℤ) - 30]
    let v : Fin n → ℤ := fun i => xs.getD i.val 0
    let out := toList (run (oddEvenSorter k) v)
    unless out == xs.mergeSort (· ≤ ·) do throw (IO.userError s!"k = {k}: {xs} gave {out}")
  let len := (oddEvenSorter k).length
  unless 4 * (len + 1) + k * 2 ^ k == (k * k + 4) * 2 ^ k do
    throw (IO.userError s!"k = {k}: {len} comparators")
  IO.println s!"{n} wires: {len} comparators (bitonic: {(bitonicSorter k).length}); sorts 200 \
    pseudo-random inputs"

#eval do for k in [1, 2, 3, 4] do checkSorter k

#eval do
  for k in [1, 2, 3] do
    unless sortsBool (oddEvenSorter k) do throw (IO.userError s!"sortsBool fails for k = {k}")
  -- the merger without its last layer does not merge
  let broken : Network 8 := ofPairs 8 (oddEvenSortN 2 ++
    relabel (fun i => 4 + i) (oddEvenSortN 2) ++ relabel (fun i => 2 * i) (oddEvenMerge 1) ++
    relabel (fun i => 2 * i + 1) (oddEvenMerge 1))
  if sortsBool broken then throw (IO.userError "the last layer is redundant?")
  IO.println "sortsBool holds on 2, 4 and 8 wires; without the last merge layer it fails"

/-! Closed checks -/

example : Sorts (oddEvenSorter 5) ℤ := oddEvenSorter_sorts 5 ℤ

example : (oddEvenSorter 5).length = 191 := by
  have := length_oddEvenSorter 5
  omega

#print axioms oddEvenSorter_sorts
#print axioms oddEvenMerge_merges
#print axioms oddEvenSortN_sorts
#print axioms length_oddEvenSorter

end Cslib.Algorithms.Lean.SortingNetworks.OddEven
