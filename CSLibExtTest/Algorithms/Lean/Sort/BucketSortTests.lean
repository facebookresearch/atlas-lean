/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Sort.Bucket.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Floor
public meta import CSLibExt.Algorithms.Lean.Sort.Bucket.Basic
public meta import CSLibExt.Algorithms.Lean.Sort.InsertionCost
public meta import Cslib.Algorithms.Lean.Sort.Insertion
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Data.Vector.Basic
public meta import Mathlib.Data.Rat.Floor

open Set Cslib.Algorithms.Lean.TimeM

namespace BucketSortTests

private def fixture : Array Rat := #[3/4, 1/4, 1/2, 1/4]
private def emptyFixture : Array Rat := #[]
private def singletonFixture : Array Rat := #[255/256]
private def boundaryFixture : Array Rat := #[0, 1/4, 1/2, 255/256]
private def ascendingFixture : Array Rat := #[1/32, 2/32, 3/32, 4/32]
private def descendingFixture : Array Rat := #[4/32, 3/32, 2/32, 1/32]

private lemma fixture_valid : ∀ x ∈ fixture.toList, x ∈ Ico (0 : Rat) 1 := by
  norm_num [fixture, Set.mem_Ico]

private theorem empty_valid : ∀ x ∈ emptyFixture.toList, x ∈ Ico (0 : Rat) 1 := by
  simp [emptyFixture]

private theorem singleton_valid : ∀ x ∈ singletonFixture.toList, x ∈ Ico (0 : Rat) 1 := by
  norm_num [singletonFixture, Set.mem_Ico]

private theorem boundary_valid : ∀ x ∈ boundaryFixture.toList, x ∈ Ico (0 : Rat) 1 := by
  norm_num [boundaryFixture, Set.mem_Ico]

private theorem ascending_valid : ∀ x ∈ ascendingFixture.toList, x ∈ Ico (0 : Rat) 1 := by
  norm_num [ascendingFixture, Set.mem_Ico]

private theorem descending_valid : ∀ x ∈ descendingFixture.toList, x ∈ Ico (0 : Rat) 1 := by
  norm_num [descendingFixture, Set.mem_Ico]

private def check (label : String) (xs : Array Rat)
    (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : Rat) 1)
    (expectedOutput : Array Rat) (expectedTime : Nat) (mode : String) : IO Unit := do
  let actual := bucketSort xs hx
  let counts := (List.range xs.size).map (fun i => xs.toList.countP
    (fun x => decide (Nat.floor ((xs.size : Rat) * x) = i)))
  let lower := (if mode == "wrong-lower" then 6 else 5) * xs.size
  let upper := 5 * xs.size +
    (if mode == "wrong-upper" then 0 else (counts.map (fun c => c ^ 2)).sum)
  unless actual.ret == expectedOutput && actual.time == expectedTime do
    throw (IO.userError s!"output/count assertion: {label}: actual {actual.ret.toList}/{actual.time}")
  unless lower ≤ actual.time do
    throw (IO.userError s!"lower-bound assertion: {label}: {lower} > actual {actual.time}")
  unless actual.time ≤ upper do
    throw (IO.userError s!"upper-bound assertion: {label}: actual {actual.time} > {upper}")
  IO.println (s!"ACTUAL_GENERIC_BOUND {label}: {actual.ret.toList}; time={actual.time}; " ++
    s!"counts={counts}; lower={lower}; upper={upper}")

private def run (args : List String) : IO Unit := do
  let mode := args.headD "normal"
  let expected := if mode == "wrong-output" then fixture else #[1/4, 1/4, 1/2, 3/4]
  check "fractional duplicates" fixture fixture_valid expected 21 mode
  check "empty" emptyFixture empty_valid #[] 0 mode
  check "singleton" singletonFixture singleton_valid #[255/256] 5 mode
  check "four distinct bucket boundaries" boundaryFixture boundary_valid boundaryFixture 20 mode
  check "ascending source, descending saved bucket" ascendingFixture ascending_valid
    ascendingFixture 26 mode
  check "descending source, ascending saved bucket" descendingFixture descending_valid
    ascendingFixture 23 mode

#eval run []

end BucketSortTests
