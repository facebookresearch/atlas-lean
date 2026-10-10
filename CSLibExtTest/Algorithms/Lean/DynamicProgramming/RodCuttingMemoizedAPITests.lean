/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.RodCuttingMemoized

set_option autoImplicit false

open Cslib.Algorithms.Lean.RodCutting

universe u

#check @memoizedCutRodAux
#check @memoizedCutRod
#check @memoizedCutRodAux_hit
#check @memoizedCutRodAux_preserves
#check @memoizedCutRodAux_correct
#check @memoizedCutRod_zero
#check @memoizedCutRod_correct
#check @memoizedCutRodAux_complete
#check @memoizedCutRod_time

example {α : Type u} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
    {n : Nat} (prices : Vector α n) :
    IsGreatest (Set.range fun parts : Composition n => compositionRevenue prices parts le_rfl)
      (memoizedCutRod prices).ret := memoizedCutRod_correct prices

example {α : Type u} [AddCommMonoid α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) (j : Nat) (hjn : j ≤ n) (cache : Vector (Option α) (n + 1))
    (value : α) (hcache : cache[j]'(by omega) = some value) :
    (memoizedCutRodAux prices j hjn cache).time = 1 := by
  rw [memoizedCutRodAux_hit prices j hjn cache value hcache]

example {α : Type u} [AddCommMonoid α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) (j : Nat) (hjn : j ≤ n) (cache : Vector (Option α) (n + 1))
    (k : Nat) (hkn : k ≤ n) (hjk : j < k) :
    (memoizedCutRodAux prices j hjn cache).ret.2[k]'(by omega) = cache[k] :=
  (memoizedCutRodAux_preserves prices j hjn cache).2 k hkn hjk

example {α : Type u} [AddCommMonoid α] [LinearOrder α] (prices : Vector α 0) :
    (memoizedCutRod prices).ret = 0 ∧ (memoizedCutRod prices).time = 2 := by
  rw [memoizedCutRod_zero]
  exact ⟨rfl, rfl⟩

example {α : Type u} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hjn : j ≤ n) (k : Nat) (hkj : k ≤ j) :
    ∃ value : α,
      (memoizedCutRodAux prices j hjn (Vector.replicate (n + 1) none)).ret.2[k]'(by omega) =
        some value ∧
      IsGreatest (Set.range fun parts : Composition k =>
        compositionRevenue prices parts (by omega)) value :=
  memoizedCutRodAux_complete prices j hjn k hkj

example {α : Type u} [AddCommMonoid α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) : (memoizedCutRod prices).time = n ^ 2 + 2 * n + 2 :=
  memoizedCutRod_time prices
