/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import MathlibExt.Data.Multiset.Scan
public meta import Mathlib.Data.Multiset.ZeroCons

/-! # Executable boundary checks for the ported submultiset scan -/

@[expose] public section

/-- info: [] -/
#guard_msgs in
#eval (Multiset.scanToList ([] : List Nat) 0 (by decide)).val

/-- info: [] -/
#guard_msgs in
#eval (Multiset.scanToList [1, 2, 1] 0 (by decide)).val

/-- info: [2, 2, 3] -/
#guard_msgs in
#eval (Multiset.scanToList [2, 1, 2, 3] ({2, 2, 3} : Multiset Nat)
  (by decide)).val

/-- info: [1, 2] -/
#guard_msgs in
#eval (Multiset.scanToList [1, 2, 3] ({2, 1} : Multiset Nat)
  (by decide)).val

example {α : Type*} [DecidableEq α] (l : List α) (s : Multiset α)
    (h : s ≤ (l : Multiset α)) :
    ((Multiset.scanToList l s h).val : Multiset α) = s :=
  (Multiset.scanToList l s h).property
