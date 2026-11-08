/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DynamicProgramming.ExactSubsetSum

/-! Ordinary consumers of the two executors and sixteen public theorems. -/

open Cslib.Algorithms.Lean.ExactSubsetSum

#check @exactSubsetSumSums
#check @exactSubsetSum
#check @exactSubsetSumSums_mem
#check @exactSubsetSumSums_sorted
#check @exactSubsetSumSums_zero_mem
#check @exactSubsetSum_ret
#check @exactSubsetSum_optimal
#check @exactSubsetSum_optimal_of_positive
#check @exactSubsetSum_time
#check @exactSubsetSumSums_length_le_pow
#check @exactSubsetSumSums_length_le_target
#check @exactSubsetSumSums_length_le_sum
#check @exactSubsetSum_time_le_exponential
#check @exactSubsetSum_time_le_numeric
#check @exactSubsetSumSums_powers_of_two
#check @exactSubsetSum_time_ge_powers_of_two
#check @exactSubsetSum_time_le_of_target_le_pow
#check @exactSubsetSum_time_le_of_values_le_pow

example (xs : List Nat) (target z : Nat) :
    z ∈ (exactSubsetSumSums xs target).ret ↔
      z ≤ target ∧ ∃ ys : List Nat, ys.Sublist xs ∧ ys.sum = z :=
  exactSubsetSumSums_mem xs target z

example (xs : List Nat) (target : Nat) :
    (∃ ys : List Nat, ys.Sublist xs ∧ ys.sum = (exactSubsetSum xs target).ret) ∧
      (exactSubsetSum xs target).ret ≤ target ∧
      ∀ ys : List Nat, ys.Sublist xs → ys.sum ≤ target →
        ys.sum ≤ (exactSubsetSum xs target).ret :=
  exactSubsetSum_optimal xs target

example (xs : List Nat) (target : Nat) (h : xs.Nodup)
    (hp : ∀ x ∈ xs, 0 < x) (ht : 0 < target) :
    (∃ ys : List Nat, ys.Sublist xs ∧ ys.sum = (exactSubsetSum xs target).ret) ∧
      (exactSubsetSum xs target).ret ≤ target ∧
      ∀ ys : List Nat, ys.Sublist xs → ys.sum ≤ target →
        ys.sum ≤ (exactSubsetSum xs target).ret :=
  exactSubsetSum_optimal_of_positive xs target h hp ht

example :
    (∃ ys : List Nat, ys.Sublist [0, 2, 2, 0] ∧
      ys.sum = (exactSubsetSum [0, 2, 2, 0] 3).ret) ∧
      (exactSubsetSum [0, 2, 2, 0] 3).ret ≤ 3 ∧
      ∀ ys : List Nat, ys.Sublist [0, 2, 2, 0] → ys.sum ≤ 3 →
        ys.sum ≤ (exactSubsetSum [0, 2, 2, 0] 3).ret :=
  exactSubsetSum_optimal [0, 2, 2, 0] 3

example (xs : List Nat) :
    (exactSubsetSum xs 0).ret ≤ 0 ∧
      ∀ ys : List Nat, ys.Sublist xs → ys.sum ≤ 0 →
        ys.sum ≤ (exactSubsetSum xs 0).ret :=
  (exactSubsetSum_optimal xs 0).2

example (xs : List Nat) (target : Nat) :
    (exactSubsetSum xs target).time ≤
      1 + xs.length + 7 * (2 ^ xs.length - 1) + 2 ^ xs.length :=
  exactSubsetSum_time_le_exponential xs target

example (xs : List Nat) (target : Nat) :
    (exactSubsetSum xs target).time ≤
      1 + xs.length + (7 * xs.length + 1) * min (target + 1) (xs.sum + 1) :=
  exactSubsetSum_time_le_numeric xs target

example (n i : Nat) (h : i ≤ n) :
    (exactSubsetSumSums (((List.range n).map (fun j => 2 ^ j)).take i)
      (2 ^ n - 1)).ret = List.range (2 ^ i) :=
  exactSubsetSumSums_powers_of_two n i h

example (n : Nat) : 2 ^ n - 1 ≤
    (exactSubsetSum ((List.range n).map (fun j => 2 ^ j)) (2 ^ n - 1)).time :=
  exactSubsetSum_time_ge_powers_of_two n
