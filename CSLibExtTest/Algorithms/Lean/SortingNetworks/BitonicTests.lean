/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.Bitonic
public meta import CSLibExt.Algorithms.Lean.SortingNetworks.Bitonic
public import Mathlib.Data.Int.Order.Basic
public meta import Mathlib.Data.Int.Order.Basic

/-!
# Bitonic sorter tests

Executed fixtures: Batcher's network on `2`, `4`, `8` and `16` wires sorts 200 pseudo-random
integer inputs each (output equal to the sorted input), passes `sortsBool` (all Boolean inputs) on
up to `8` wires, and has `k (k + 1) 2 ^ k / 4` comparators; the bitonic merger alone sorts every
bitonic Boolean input on `8` wires but not every Boolean input (a witness is printed), as
`bitonicMerge_sorts` requires. Each run throws on failure. Closed checks instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.SortingNetworks.Bitonic

private meta def toList {n : ℕ} (v : Fin n → ℤ) : List ℤ := (List.finRange n).map v

private meta def checkSorter (k : ℕ) : IO Unit := do
  let n := 2 ^ k
  let mut s := 11
  for _ in [0:200] do
    let mut xs : List ℤ := []
    for _ in [0:n] do
      s := (s * 1103515245 + 12345) % 2147483648
      xs := xs ++ [((s / 7 % 61 : ℕ) : ℤ) - 30]
    let v : Fin n → ℤ := fun i => xs.getD i.val 0
    let out := toList (run (bitonicSorter k) v)
    unless out == xs.mergeSort (· ≤ ·) do
      throw (IO.userError s!"k = {k}: {xs} gave {out}")
  unless 4 * (bitonicSorter k).length == k * (k + 1) * 2 ^ k do
    throw (IO.userError s!"k = {k}: {(bitonicSorter k).length} comparators")
  IO.println s!"{n} wires: {(bitonicSorter k).length} comparators; sorts 200 pseudo-random inputs"

#eval do for k in [1, 2, 3, 4] do checkSorter k

#eval do
  for k in [1, 2, 3] do
    unless sortsBool (bitonicSorter k) do throw (IO.userError s!"sortsBool fails for k = {k}")
  IO.println "sortsBool holds for the bitonic sorter on 2, 4 and 8 wires"

-- the merger sorts bitonic inputs only
#eval do
  let net := bitonicMerge 3 0
  let mut bitonic := 0
  let mut witness : Option (List Bool) := none
  for m in List.range 256 do
    let f : ℕ → Bool := fun i => Nat.testBit m i
    let xs := (List.range 8).map f
    let changes := ((List.range 7).filter fun i => f i != f (i + 1)).length
    let out := runN net f
    let sorted := (List.range 7).all fun i => out i ≤ out (i + 1)
    if changes ≤ 2 then
      bitonic := bitonic + 1
      unless sorted do throw (IO.userError s!"the merger leaves bitonic {xs} unsorted")
    else if !sorted && witness.isNone then witness := some xs
  IO.println s!"8-wire bitonic merger: sorts all {bitonic} bitonic Boolean inputs; \
    leaves the non-bitonic {witness} unsorted"

/-! Closed checks -/

example : Sorts (bitonicSorter 5) ℤ := bitonicSorter_sorts 5 ℤ

example : 4 * (bitonicSorter 5).length = 5 * 6 * 32 := length_bitonicSorter 5

#print axioms bitonicSorter_sorts
#print axioms bitonicSortN_sorts
#print axioms bitonicMerge_sorts
#print axioms halfClean_bitonic
#print axioms length_bitonicSorter

end Cslib.Algorithms.Lean.SortingNetworks.Bitonic
