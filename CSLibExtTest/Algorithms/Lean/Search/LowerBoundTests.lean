/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Search.LowerBound

import Mathlib.Tactic.NormNum

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM

universe u

example {α : Type u} [LinearOrder α] (xs : Array α) (key : α) : TimeM Nat Nat :=
  lowerBound xs key

example : (lowerBound (#[] : Array Nat) 3).ret = 0 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound (#[] : Array Nat) 3).time = 0 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]

example : (lowerBound #[4] 4).ret = 0 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound #[4] 3).ret = 0 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound #[4] 5).ret = 1 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound #[4] 5).time = 1 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? #[4] 4).ret = some 0 := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? #[4] 3).ret = none := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? #[4] 5).ret = none := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]

example : (lowerBound #[1, 2, 3] 9).ret = 3 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound #[4, 5, 6] 1).ret = 0 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]

example : (lowerBound #[2, 2, 2, 4] 2).ret = 0 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound #[1, 3, 3, 3, 5] 3).ret = 1 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound #[1, 2, 4, 4] 4).ret = 2 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]

example : (binarySearchFirst? #[2, 2, 2, 4] 2).ret = some 0 := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? #[1, 3, 3, 3, 5] 3).ret = some 1 := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? #[1, 3, 3, 3, 5] 3).time = 4 := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? #[1, 2, 4, 4] 4).ret = some 2 := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? #[1, 3, 3, 3, 5] 4).ret = none := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? #[1, 3, 3, 3, 5] 4).time = 4 := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? #[1, 3, 3, 3, 5] 9).time = 2 := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? (#[] : Array Nat) 4).ret = none := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]
example : (binarySearchFirst? (#[] : Array Nat) 4).time = 0 := by
  norm_num [binarySearchFirst?, lowerBound, lowerBound.loop.eq_def]

example : (lowerBound (Array.replicate 1 0) 0).time = 1 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound (Array.replicate 2 0) 0).time = 2 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound (Array.replicate 3 0) 0).time = 2 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound (Array.replicate 4 0) 0).time = 3 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound #[0, 0, 0, 0] 1).time = 2 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound (Array.replicate 7 0) 0).time = 3 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound (Array.replicate 8 0) 0).time = 4 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]
example : (lowerBound (Array.replicate 9 0) 0).time = 4 := by
  norm_num [lowerBound, lowerBound.loop.eq_def]

example (xs : Array Nat) (key : Nat) (hs : xs.Pairwise (fun x y => x ≤ y)) :
    (lowerBound xs key).ret ≤ xs.size ∧
      (∀ j (_hj : j < (lowerBound xs key).ret) (_hjs : j < xs.size), xs[j] < key) ∧
      (∀ j (_hj : (lowerBound xs key).ret ≤ j) (_hjs : j < xs.size), key ≤ xs[j]) :=
  lowerBound_spec xs key hs

example (xs : Array Nat) (key : Nat) :
    (lowerBound xs key).time ≤ Nat.clog 2 (xs.size + 1) :=
  lowerBound_time_le xs key

example (xs : Array Nat) (key : Nat) (hs : xs.Pairwise (fun x y => x ≤ y)) :
    (binarySearchFirst? xs key).ret = none ↔
      ∀ i (hi : i < xs.size), xs[i] ≠ key :=
  binarySearchFirst?_eq_none_iff xs key hs

example (xs : Array Nat) (key : Nat) (hs : xs.Pairwise (fun x y => x ≤ y)) (i : Nat) :
    (binarySearchFirst? xs key).ret = some i ↔
      ∃ hi : i < xs.size,
        xs[i] = key ∧
          ∀ j (_hj : j < i) (_hjs : j < xs.size), xs[j] < key :=
  binarySearchFirst?_eq_some_iff xs key hs i

example (xs : Array Nat) (key : Nat) :
    (binarySearchFirst? xs key).time ≤ Nat.clog 2 (xs.size + 1) + 1 :=
  binarySearchFirst?_time_le xs key

example (xs : Array Nat) (key : Nat) :
    (binarySearchFirst? xs key).time =
      (lowerBound xs key).time + if (lowerBound xs key).ret < xs.size then 1 else 0 :=
  binarySearchFirst?_time xs key

end Cslib.Algorithms.Lean.TimeM
