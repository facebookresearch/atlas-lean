/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.RodCutting

/-! Ordinary-import access to every reconstruction result, without exposing internal helpers. -/

set_option autoImplicit false

universe u

open Cslib.Algorithms.Lean.RodCutting

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.RodCutting.scanCutsWithIndex

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.RodCutting.fillRowsWithCuts

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.RodCutting.FirstCutsValid

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.RodCutting.reconstructCuts

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.RodCutting.reconstructCuts._unary

example {α : Type u} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
    {n : Nat} (prices : Vector α n) (j : Nat) (hj : j ≤ n) :
    IsGreatest (Set.range fun parts : Composition j => compositionRevenue prices parts hj)
      (extendedBottomUpCutRod prices).ret.1[j] :=
  extendedBottomUpCutRod_correct prices j hj

example {α : Type (u + 1)} [AddCommMonoid α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) (j : Nat) (hpos : 0 < j) (hj : j ≤ n) :
    ∃ i : Fin j, (extendedBottomUpCutRod prices).ret.2[j - 1]'(by omega) = i.val + 1 ∧
      prices[i.val]'(by omega) +
        (extendedBottomUpCutRod prices).ret.1[j - (i.val + 1)]'(by omega) =
        (extendedBottomUpCutRod prices).ret.1[j] ∧
      ∀ h : Fin j, h.val < i.val →
        prices[h.val]'(by omega) +
          (extendedBottomUpCutRod prices).ret.1[j - (h.val + 1)]'(by omega) <
          (extendedBottomUpCutRod prices).ret.1[j] :=
  extendedBottomUpCutRod_firstCut prices j hpos hj

example {α : Type u} [AddCommMonoid α] [LinearOrder α] {n : Nat} (prices : Vector α n) :
    (extendedBottomUpCutRod prices).ret.1[n] = (bottomUpCutRod prices).ret :=
  extendedBottomUpCutRod_revenue_eq prices

example {α : Type u} [AddCommMonoid α] [LinearOrder α] {n : Nat} (prices : Vector α n) :
    (extendedBottomUpCutRod prices).time = n * (n + 1) / 2 :=
  extendedBottomUpCutRod_time prices

example {α : Type u} [AddCommMonoid α] [LinearOrder α] :
    extendedBottomUpCutRod (#v[] : Vector α 0) =
      pure (Vector.replicate 1 0, Vector.replicate 0 0) :=
  extendedBottomUpCutRod_zero (#v[] : Vector α 0)

example {α : Type (u + 1)} [AddCommMonoid α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) (i : Nat) (hi : i < (cutRodSolution prices).ret.length) :
    (extendedBottomUpCutRod prices).ret.2[n - (cutRodSolution prices).ret.sizeUpTo i - 1]? =
      some ((cutRodSolution prices).ret.blocks[i]'hi) := cutRodSolution_blocks prices i hi

example {α : Type u} [AddCommMonoid α] [LinearOrder α] {n : Nat} (prices : Vector α n) :
    compositionRevenue prices (cutRodSolution prices).ret le_rfl =
      (extendedBottomUpCutRod prices).ret.1[n] := cutRodSolution_revenue prices

example {α : Type u} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
    {n : Nat} (prices : Vector α n) :
    IsGreatest (Set.range fun parts : Composition n => compositionRevenue prices parts le_rfl)
      (compositionRevenue prices (cutRodSolution prices).ret le_rfl) := cutRodSolution_correct prices

example {α : Type u} [AddCommMonoid α] [LinearOrder α] {n : Nat} (prices : Vector α n) :
    (cutRodSolution prices).time = n * (n + 1) / 2 + (cutRodSolution prices).ret.length :=
  cutRodSolution_time prices

example {α : Type (u + 1)} [AddCommMonoid α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) : (cutRodSolution prices).ret.length ≤ n :=
  (cutRodSolution prices).ret.length_le

example {α : Type u} [AddCommMonoid α] [LinearOrder α] {n : Nat} (prices : Vector α n) :
    (cutRodSolution prices).time ≤ n * (n + 1) / 2 + n := by
  rw [cutRodSolution_time]
  exact Nat.add_le_add_left (cutRodSolution prices).ret.length_le _

example {α : Type u} [AddCommMonoid α] [LinearOrder α] :
    cutRodSolution (#v[] : Vector α 0) = pure (Composition.ones 0) := cutRodSolution_zero
