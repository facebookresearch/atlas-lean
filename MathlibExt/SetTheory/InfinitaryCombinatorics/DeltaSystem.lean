/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Data.Set.Basic
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 11
-- Proposed path (advisory metadata only, not a review instruction).

-- Logic 11: A Delta system
def IsDeltaSystem {α : Type*} (A : Set (Set α)) (r : Set α) : Prop :=
    A.Pairwise fun s t => s ∩ t = r


theorem IsDeltaSystem.root_subset {α : Type*} {A : Set (Set α)} {r s t : Set α}
    (h : IsDeltaSystem A r) (hs : s ∈ A) (ht : t ∈ A) (hst : s ≠ t) : r ⊆ s := by
  rw [← h hs ht hst]
  exact Set.inter_subset_left


theorem IsDeltaSystem.root_unique {α : Type*} {A : Set (Set α)} {r r' s t : Set α}
    (h : IsDeltaSystem A r) (h' : IsDeltaSystem A r') (hs : s ∈ A) (ht : t ∈ A) (hst : s ≠ t) :
    r = r' :=
  (h hs ht hst).symm.trans (h' hs ht hst)


def petal (n : ℕ) : Set ℕ := {0, n + 1}


def triangle : Set (Set ℕ) := {{0, 1}, {1, 2}, {0, 2}}

end
