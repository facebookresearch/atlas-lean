/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Search.LowerBound
public meta import CSLibExt.Algorithms.Lean.Search.LowerBound

/-! Runtime agreement with independent forward scans on sorted integer fixtures. -/

open Cslib.Algorithms.Lean.TimeM

namespace LowerBoundRuntimeTests

private def insertionScan (xs : Array Int) (key : Int) : Nat := Id.run do
  let mut i := 0
  for x in xs do
    if key ≤ x then return i
    i := i + 1
  return xs.size

private def equalityScan (xs : Array Int) (key : Int) : Option Nat := Id.run do
  let mut i := 0
  for x in xs do
    if x == key then return some i
    i := i + 1
  return none

private def sorted (xs : Array Int) : Bool :=
  decide (xs.toList.Pairwise (fun x y => x ≤ y))

private def accepts (xs : Array Int) (key : Int) (index : Nat)
    (member : Option Nat) : Bool :=
  sorted xs && index == insertionScan xs key && member == equalityScan xs key

-- Each expected pair is fixed by counting preceding entries and locating the first equality.
private def fixtures : List (Array Int × Int × Nat × Option Nat) :=
  let b : Int := 10000000000000000000000000000000000000000
  [(#[], 0, 0, none),
   (#[-2], -3, 0, none), (#[-2], -2, 0, some 0), (#[-2], -1, 1, none),
   (#[-5, 0, 6], -6, 0, none), (#[-5, 0, 6], 7, 3, none),
   (#[-4, -4, 2], -4, 0, some 0), (#[-8, -1, -1, -1, 5], -1, 1, some 1),
   (#[-9, -3, 0, 4, 12], -2, 2, none), (#[-9, -3, 0, 4, 12], 0, 2, some 2),
   (#[-b - 2, -b, -b + 2, 0, b - 2, b, b + 2], -b - 1, 1, none),
   (#[-b - 2, -b, -b + 2, 0, b - 2, b, b + 2], -b, 1, some 1),
   (#[-b - 2, -b, -b + 2, 0, b - 2, b, b + 2], b - 1, 5, none),
   (#[-b - 2, -b, -b + 2, 0, b - 2, b, b + 2], b, 5, some 5),
   (#[-b - 2, -b, -b + 2, 0, b - 2, b, b + 2], -b - 3, 0, none),
   (#[-b - 2, -b, -b + 2, 0, b - 2, b, b + 2], b + 3, 7, none),
   (#[-2, 2], 0, 1, none), (#[-3, -1, 1, 3], 1, 2, some 2),
   (#[-6, -4, -2, 0, 2, 4, 6], 5, 6, none),
   (#[-8, -6, -4, -2, 0, 2, 4, 6], 1, 5, none),
   (#[-8, -6, -4, -2, 0, 2, 4, 6], 6, 7, some 7),
   (#[-8, -6, -4, -2, 0, 2, 4, 6, 8], 8, 8, some 8)]

private def controls : List (String × Array Int × Int × Nat × Option Nat) :=
  [("shifted-insertion", #[-8, -1, -1, -1, 5], -1, 2, some 1),
   ("later-duplicate", #[-8, -1, -1, -1, 5], -1, 1, some 2),
   ("false-absence", #[-8, -1, -1, -1, 5], -1, 1, none),
   ("in-range-false-presence", #[-9, -3, 0, 4, 12], -2, 2, some 2)]

#eval do
  let mut cases := 0
  let mut equal := 0
  let mut unequal := 0
  let mut outside := 0
  for (xs, key, index, member) in fixtures do
    unless sorted xs && insertionScan xs key == index && equalityScan xs key == member do
      throw (IO.userError s!"oracle anchor mismatch: {xs}, key={key}")
    let gotIndex := (lowerBound xs key).ret
    let gotMember := (binarySearchFirst? xs key).ret
    unless accepts xs key gotIndex gotMember do
      throw (IO.userError s!"search mismatch: {xs}, key={key}, {gotIndex}, {gotMember}")
    let outcome := if h : gotIndex < xs.size then
      if xs[gotIndex] == key then "valid+equal" else "valid+unequal"
      else "out-of-range"
    if outcome == "valid+equal" then equal := equal + 1
    if outcome == "valid+unequal" then unequal := unequal + 1
    if outcome == "out-of-range" then outside := outside + 1
    IO.println s!"WITNESS {outcome}: key={key}, size={xs.size}, index={gotIndex}, member={gotMember}"
    cases := cases + 1
  let mut rejected := 0
  for (label, xs, key, wrongIndex, wrongMember) in controls do
    let gotIndex := (lowerBound xs key).ret
    let gotMember := (binarySearchFirst? xs key).ret
    unless accepts xs key gotIndex gotMember do
      throw (IO.userError s!"control baseline failed: {label}")
    if accepts xs key wrongIndex wrongMember then
      throw (IO.userError s!"wrong observation accepted: {label}")
    IO.println s!"REJECT {label}: baseline=({gotIndex}, {gotMember}), wrong=({wrongIndex}, {wrongMember})"
    rejected := rejected + 1
  unless cases == 22 && rejected == 4 && equal > 0 && unequal > 0 && outside > 0 do
    throw (IO.userError "missing case, control or wrapper outcome")
  IO.println s!"PASS cases={cases}, anchors={cases}, controls={rejected}, control-baselines={rejected}"
  IO.println s!"OUTCOMES valid+equal={equal}, valid+unequal={unequal}, out-of-range={outside}"

end LowerBoundRuntimeTests
