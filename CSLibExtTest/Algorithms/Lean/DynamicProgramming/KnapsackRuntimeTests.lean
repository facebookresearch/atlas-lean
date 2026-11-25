/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DynamicProgramming.Knapsack
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin
meta import CSLibExt.Algorithms.Lean.DynamicProgramming.Knapsack
meta import Mathlib.Data.Finset.Powerset
meta import Mathlib.Data.Finset.Lattice.Fold
meta import Mathlib.Data.Fintype.Fin
meta import Plausible.Random

/-!
# Knapsack returned-witness runtime tests

Execute `(solve items capacity).ret` and check all of `solve_correct`: feasibility,
reported value equals the selected sum, and optimality over all feasible subsets.
The result type already guarantees distinct, bounded original indices; equal item
records are not collapsed. No particular tied optimum is required.

The private enumeration uses the same powerset, weight filter and value sum as
`KnapsackScaling.optVal`, the existing noncomputable specification. It does not
copy the solver's dynamic-programming recurrence. Sixteen literal optima and counts
of optimal subsets anchor the enumeration, including zero weights/values, slack,
non-greedy optima and arbitrary-precision values.

The corpus has all 1,295 list/capacity pairs with lists of length at most three over
the six items with weight in 0..2 and value in {0,2}, and capacities 0..4, plus 192 Plausible
samples (seed 2026111902). Six equal strata cover independent inputs, capacity zero,
duplicates, ties, slack and all-too-heavy items. Samples have length at most seven,
weight at most 28, value at most 31 and capacity at most 54; no retries or discards.
Printed bins describe inputs and returned sets, not internal branch coverage.
Finite agreement is not a universal theorem, a cost check or a machine-time bound.

Replay from the repository root:
```
lake --wfail build CSLibExtTest.Algorithms.Lean.DynamicProgramming.KnapsackRuntimeTests
lake env lean -DwarningAsError=true CSLibExtTest/Algorithms/Lean/DynamicProgramming/KnapsackRuntimeTests.lean
```
-/

open Cslib.Algorithms.Lean.TimeM.Knapsack

private meta def feasibleSubsets (items : List Item) (capacity : Nat) :
    Finset (Finset (Fin items.length)) :=
  Finset.univ.powerset.filter (fun s => totalWeight items s ≤ capacity)

private meta def checkCase (items : List Item) (capacity : Nat)
    (actual : Result items) : IO (Nat × Nat) := do
  letI : Decidable (Feasible items capacity actual.chosen) :=
    inferInstanceAs (Decidable (totalWeight items actual.chosen ≤ capacity))
  unless decide (Feasible items capacity actual.chosen) do
    throw (IO.userError s!"infeasible witness: items={repr items} capacity={capacity} \
      weight={totalWeight items actual.chosen} report={actual.value}")
  let selectedValue := totalValue items actual.chosen
  unless actual.value == selectedValue do
    throw (IO.userError s!"reported-value mismatch: items={repr items} capacity={capacity} \
      selected={selectedValue} report={actual.value}")
  let feasible := feasibleSubsets items capacity
  let optimum := feasible.sup (totalValue items)
  unless actual.value == optimum do
    throw (IO.userError s!"suboptimal witness: items={repr items} capacity={capacity} \
      optimum={optimum} report={actual.value}")
  return (optimum, (feasible.filter (fun s => totalValue items s = optimum)).card)

private meta def literals : List (List Item × Nat × Nat × Nat) :=
  [([], 0, 0, 1),
   ([], 7, 0, 1),
   ([⟨4, 7⟩], 4, 7, 1),
   ([⟨4, 7⟩], 3, 0, 1),
   ([⟨0, 4⟩, ⟨0, 5⟩], 0, 9, 1),
   ([⟨0, 0⟩, ⟨3, 0⟩], 3, 0, 4),
   ([⟨2, 5⟩, ⟨2, 5⟩], 2, 5, 2),
   ([⟨2, 5⟩, ⟨2, 5⟩], 4, 10, 1),
   ([⟨2, 5⟩, ⟨4, 6⟩], 3, 5, 1),
   ([⟨1, 9⟩, ⟨2, 3⟩], 2, 9, 1),
   ([⟨2, 3⟩, ⟨1, 9⟩], 2, 9, 1),
   ([⟨1, 5⟩, ⟨5, 1⟩, ⟨1, 7⟩], 2, 12, 1),
   ([⟨10, 60⟩, ⟨20, 100⟩, ⟨30, 120⟩], 50, 220, 1),
   ([⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩], 6, 8, 1),
   ([⟨5, 257⟩, ⟨7, 65537⟩, ⟨13, 131⟩], 12, 65794, 1),
   ([⟨0, 18446744073709551616⟩, ⟨1, 18446744073709551617⟩, ⟨2, 1⟩],
     1, 36893488147419103233, 1)]

private meta def itemLists : Nat → List (List Item)
  | 0 => [[]]
  | n + 1 =>
    ([⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 0⟩, ⟨2, 2⟩] : List Item).flatMap
      fun item => (itemLists n).map (item :: ·)

private meta def exhaustiveInputs : List (List Item × Nat) :=
  ((List.range 4).flatMap itemLists).flatMap fun items =>
    (List.range 5).map (items, ·)

private meta def chooseUpTo (n : Nat) : Plausible.Rand Nat := do
  return (← Plausible.Random.randBound Nat 0 n (Nat.zero_le n)).val

private meta def randomItems (n : Nat) : Plausible.Rand (List Item) :=
  (List.range n).mapM fun _ => do
    return ⟨← chooseUpTo 9, ← chooseUpTo 30⟩

private meta def sample (stratum : Nat) : Plausible.Rand (List Item × Nat) := do
  match stratum with
  | 0 =>
    let n ← chooseUpTo 7
    let items ← randomItems n
    return (items, ← chooseUpTo 18)
  | 1 =>
    let n := (← chooseUpTo 5) + 2
    let v := (← chooseUpTo 30) + 1
    return (⟨0, v⟩ :: (← randomItems (n - 1)), 0)
  | 2 =>
    let n := (← chooseUpTo 4) + 2
    let w := (← chooseUpTo 8) + 1
    let v := (← chooseUpTo 30) + 1
    return (List.replicate n ⟨w, v⟩, w * (← chooseUpTo n))
  | 3 =>
    let w := (← chooseUpTo 8) + 1
    let v := (← chooseUpTo 30) + 1
    return ([⟨w, v⟩, ⟨w, v⟩, ⟨w + 1, 0⟩], w)
  | 4 =>
    let w := (← chooseUpTo 7) + 1
    let v := (← chooseUpTo 29) + 1
    return ([⟨2 * w, v⟩, ⟨2 * w, v + 1⟩], 2 * w + 1)
  | _ =>
    let n := (← chooseUpTo 6) + 1
    let capacity ← chooseUpTo 18
    let items ← (List.range n).mapM fun _ => do
      return (⟨capacity + 1 + (← chooseUpTo 9), (← chooseUpTo 30) + 1⟩ : Item)
    return (items, capacity)

private meta def generatedInputs : Plausible.Rand (List (List (List Item × Nat))) :=
  (List.range 6).mapM fun stratum =>
    (List.range 32).mapM fun _ => sample stratum

private meta def shapeNames : List String :=
  ["empty", "capacityZero", "positiveZeroWeight", "zeroValue", "duplicateRecords",
   "multipleOptima", "slackPositive", "allTooHeavy", "exactFitPositive",
   "selectedEarlier", "selectedLater", "ordinaryValues", "arbitraryPrecisionValue"]

private meta def shapes (items : List Item) (capacity ways : Nat)
    (actual : Result items) : List Bool :=
  [items.isEmpty,
   capacity == 0,
   items.any (fun item => item.weight == 0 && item.value > 0),
   items.any (fun item => item.value == 0),
   items.eraseDups.length < items.length,
   ways > 1,
   actual.value > 0 && totalWeight items actual.chosen < capacity,
   !items.isEmpty && items.all (fun item => item.weight > capacity),
   actual.value > 0 && totalWeight items actual.chosen == capacity,
   (actual.chosen.filter (fun i => i.val = 0)).card > 0,
   (actual.chosen.filter (fun i => i.val + 1 = items.length)).card > 0,
   items.any (fun item => item.value > 255),
   items.any (fun item => item.value > 18446744073709551615)]

private meta def inputHash (inputs : List (List Item × Nat)) : UInt64 :=
  hash (inputs.map fun (items, capacity) =>
    (items.map (fun (item : Item) => (item.weight, item.value)), capacity))

private meta def runTests : IO Unit := do
  let exhaustive := exhaustiveInputs
  let strata := (generatedInputs.run ⟨mkStdGen 2026111902⟩).1
  let generated := strata.flatten
  unless literals.length == 16 && exhaustive.length == 1295 &&
      strata.length == 6 && strata.all (·.length == 32) && generated.length == 192 do
    throw (IO.userError "corpus cardinality")
  unless generated.all (fun (items, capacity) => items.length ≤ 7 && capacity ≤ 54 &&
      items.all (fun item => item.weight ≤ 28 && item.value ≤ 31)) do
    throw (IO.userError "generated bounds")
  let mut counts := List.replicate shapeNames.length 0
  let mut checks := 0
  for (items, capacity, expected, expectedWays) in literals do
    let actual := (solve items capacity).ret
    let (optimum, ways) ← checkCase items capacity actual
    unless optimum == expected && ways == expectedWays do
      throw (IO.userError s!"literal oracle mismatch: items={repr items} capacity={capacity} \
        expected={expected}/{expectedWays} actual={optimum}/{ways}")
    counts := counts.zipWith (fun n b => n + if b then 1 else 0)
      (shapes items capacity ways actual)
    checks := checks + 1
  for (items, capacity) in exhaustive ++ generated do
    let actual := (solve items capacity).ret
    let (_, ways) ← checkCase items capacity actual
    counts := counts.zipWith (fun n b => n + if b then 1 else 0)
      (shapes items capacity ways actual)
    checks := checks + 1
  unless checks == 1503 && counts.length == shapeNames.length && counts.all (· > 0) do
    throw (IO.userError s!"input-shape coverage: checks={checks} bins={counts}")
  let inputs := (literals.map fun (items, capacity, _, _) => (items, capacity)) ++
    exhaustive ++ generated
  IO.println s!"Knapsack returned witness: literal={literals.length} \
    exhaustive={exhaustive.length} generated={generated.length} checks={checks}"
  IO.println s!"seed=2026111902 strata={strata.map List.length} \
    sampleHash={inputHash generated} corpusHash={inputHash inputs} retries=0 discards=0"
  IO.println s!"input/result shapes={repr (shapeNames.zip counts)}"

#eval runTests
