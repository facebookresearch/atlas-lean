/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Search.Linear

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM

universe u

example : (linearSearch (fun n : Nat => n == 3) []).ret = none := by decide
example : (linearSearch (fun n : Nat => n == 3) []).time = 0 := by decide

example : (linearSearch (fun n : Nat => n == 3) [3]).ret = some 0 := by decide
example : (linearSearch (fun n : Nat => n == 3) [3]).time = 1 := by decide

example : (linearSearch (fun n : Nat => n == 3) [3, 4, 5]).ret = some 0 := by decide
example : (linearSearch (fun n : Nat => n == 3) [3, 4, 5]).time = 1 := by decide

example : (linearSearch (fun n : Nat => n == 3) [1, 2, 3, 4]).ret = some 2 := by decide
example : (linearSearch (fun n : Nat => n == 3) [1, 2, 3, 4]).time = 3 := by decide

example : (linearSearch (fun n : Nat => n == 3) [1, 2, 4]).ret = none := by decide
example : (linearSearch (fun n : Nat => n == 3) [1, 2, 4]).time = 3 := by decide

example : (linearSearch (fun n : Nat => n == 3) [1, 3, 2, 3]).ret = some 1 := by decide
example : (linearSearch (fun n : Nat => n == 3) [1, 3, 2, 3]).time = 2 := by decide

example {α : Type*} (p : α → Bool) (xs : List α) :
    (linearSearch p xs).ret = xs.findIdx? p :=
  ret_linearSearch p xs

example {α : Type*} (p : α → Bool) (xs : List α) :
    (linearSearch p xs).time ≤ xs.length :=
  linearSearch_time_le p xs

example {α : Type (u + 1)} (p : α → Bool) (xs : List α) :
    (linearSearch p xs).ret = xs.findIdx? p :=
  ret_linearSearch p xs

example {α : Type*} (p : α → Bool) (xs : List α) (i : Nat)
    (h : (linearSearch p xs).ret = some i) :
    ∃ hi : i < xs.length,
      p xs[i] = true ∧
        ∀ j (hji : j < i), p (xs[j]'(Nat.lt_trans hji hi)) = false :=
  (linearSearch_eq_some_iff p xs i).mp h

example {α : Type*} (p : α → Bool) (xs : List α)
    (h : (linearSearch p xs).ret = none) :
    (linearSearch p xs).time = xs.length :=
  linearSearch_time_eq_of_ret_eq_none p xs h

example {α : Type*} (p : α → Bool) (xs : List α) (i : Nat)
    (h : (linearSearch p xs).ret = some i) :
    (linearSearch p xs).time = i + 1 :=
  linearSearch_time_eq_of_ret_eq_some p xs i h

end Cslib.Algorithms.Lean.TimeM
