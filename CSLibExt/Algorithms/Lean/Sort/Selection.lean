/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Selection sort with an exact comparison count

This module formalizes the minimum-selection algorithm from Cormen, Leiserson, Rivest, and Stein,
*Introduction to Algorithms*, 4th ed., Section 2.2, Exercise 2.2-2. The source presents an
in-place array algorithm; here the remaining suffix is represented by a list with one minimum
removed. `List.Perm` states that this functional representation preserves the exact multiset.

The cost model charges exactly one unit for each order comparison in `extractMin`. Pattern matching,
list construction, and recursive calls are free. The exact comparison theorem refines the source's
quadratic running-time claim for this explicit cost model; it makes no claim about writes or memory.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [LinearOrder α]

/-- Extract one minimum and return the remaining elements, charging once per comparison. -/
def extractMin (candidate : α) : List α → TimeM Nat (α × List α)
  | [] => pure (candidate, [])
  | x :: xs => do
      ✓
      if x < candidate then
        let (minimum, rest) ← extractMin x xs
        return (minimum, candidate :: rest)
      else
        let (minimum, rest) ← extractMin candidate xs
        return (minimum, x :: rest)

/-- Selection sort by repeated minimum extraction. -/
def selectionSort (xs : List α) : TimeM Nat (List α) :=
  let rec loop : Nat → List α → TimeM Nat (List α)
    | 0, _ => pure []
    | _ + 1, [] => pure []
    | fuel + 1, x :: xs => do
        let (minimum, rest) ← extractMin x xs
        let sorted ← loop fuel rest
        return minimum :: sorted
  loop xs.length xs

/-- Minimum extraction compares the candidate with every remaining element exactly once. -/
@[simp]
theorem extractMin_time (candidate : α) (xs : List α) :
    (extractMin candidate xs).time = xs.length := by
  induction xs generalizing candidate with
  | nil => simp [extractMin]
  | cons x xs ih =>
      by_cases h : x < candidate
      · simp [extractMin, h, ih, Nat.add_comm]
      · simp [extractMin, h, ih, Nat.add_comm]

/-- Minimum extraction removes exactly one occurrence and preserves all other occurrences. -/
private theorem extractMin_perm (candidate : α) (xs : List α) :
    List.Perm
      ((extractMin candidate xs).ret.1 :: (extractMin candidate xs).ret.2)
      (candidate :: xs) := by
  induction xs generalizing candidate with
  | nil => simp [extractMin]
  | cons x xs ih =>
      by_cases h : x < candidate
      · simp only [extractMin, h, ↓reduceIte, ret_bind, ret_pure]
        exact (List.Perm.swap candidate _ _).trans ((ih x).cons candidate)
      · simp only [extractMin, h, ↓reduceIte, ret_bind, ret_pure]
        exact
          ((List.Perm.swap x _ _).trans ((ih candidate).cons x)).trans
            (List.Perm.swap candidate x xs)

/-- The extracted element is no greater than the candidate or any remaining input element. -/
private theorem extractMin_minimum (candidate : α) (xs : List α) :
    (extractMin candidate xs).ret.1 ≤ candidate ∧
      ∀ x ∈ xs, (extractMin candidate xs).ret.1 ≤ x := by
  induction xs generalizing candidate with
  | nil => simp [extractMin]
  | cons x xs ih =>
      by_cases h : x < candidate
      · simp only [extractMin, h, ↓reduceIte, ret_bind, ret_pure, List.forall_mem_cons]
        obtain ⟨hmin, hall⟩ := ih x
        exact ⟨hmin.trans h.le, hmin, hall⟩
      · simp only [extractMin, h, ↓reduceIte, ret_bind, ret_pure, List.forall_mem_cons]
        obtain ⟨hmin, hall⟩ := ih candidate
        exact ⟨hmin, hmin.trans (le_of_not_gt h), hall⟩

/-- Minimum extraction returns one minimum together with exactly the other input occurrences. -/
theorem extractMin_correct (candidate : α) (xs : List α) :
    List.Perm
        ((extractMin candidate xs).ret.1 :: (extractMin candidate xs).ret.2)
        (candidate :: xs) ∧
      (extractMin candidate xs).ret.1 ≤ candidate ∧
      ∀ x ∈ xs, (extractMin candidate xs).ret.1 ≤ x :=
  ⟨extractMin_perm candidate xs, extractMin_minimum candidate xs⟩

/-- Minimum extraction leaves exactly as many elements as followed the initial candidate. -/
@[simp]
private theorem extractMin_rest_length (candidate : α) (xs : List α) :
    (extractMin candidate xs).ret.2.length = xs.length := by
  have h := (extractMin_perm candidate xs).length_eq
  simpa only [List.length_cons, Nat.succ.injEq] using h

/-- Selection sort returns a nondecreasing permutation, preserving duplicate multiplicities. -/
theorem selectionSort_correct (xs : List α) :
    List.Pairwise (fun x y => x ≤ y) (selectionSort xs).ret ∧
      List.Perm (selectionSort xs).ret xs := by
  unfold selectionSort
  have loop_correct : ∀ (fuel : Nat) (ys : List α), ys.length = fuel →
      List.Pairwise (fun x y => x ≤ y) (selectionSort.loop fuel ys).ret ∧
        List.Perm (selectionSort.loop fuel ys).ret ys := by
    intro fuel
    induction fuel with
    | zero =>
        intro ys hlen
        cases ys with
        | nil => simp [selectionSort.loop]
        | cons y ys => simp at hlen
    | succ fuel ih =>
        intro ys hlen
        cases ys with
        | nil => simp [selectionSort.loop]
        | cons x xs =>
            have hxlen : xs.length = fuel := by
              simpa only [List.length_cons, Nat.succ.injEq] using hlen
            generalize hresult : (extractMin x xs).ret = result
            rcases result with ⟨minimum, rest⟩
            have hrest : rest.length = fuel := by
              rw [← hxlen, ← extractMin_rest_length x xs, hresult]
            obtain ⟨hsorted, hperm⟩ := ih rest hrest
            have hextract := extractMin_perm x xs
            rw [hresult] at hextract
            have hminimum := extractMin_minimum x xs
            rw [hresult] at hminimum
            have hle : ∀ y ∈ rest, minimum ≤ y := by
              intro y hy
              have hyInput : y ∈ x :: xs :=
                hextract.mem_iff.mp (by simp [hy])
              rcases List.mem_cons.mp hyInput with hyx | hyxs
              · rw [hyx]
                exact hminimum.1
              · exact hminimum.2 y hyxs
            have hsortedCons :
                List.Pairwise (fun a b : α => a ≤ b)
                  (minimum :: (selectionSort.loop fuel rest).ret) :=
              List.pairwise_cons.2 ⟨fun y hy => hle y (hperm.mem_iff.mp hy), hsorted⟩
            have hpermCons :
                List.Perm (minimum :: (selectionSort.loop fuel rest).ret) (x :: xs) :=
              (hperm.cons minimum).trans hextract
            simpa only [selectionSort.loop, ret_bind, ret_pure, hresult] using
              And.intro hsortedCons hpermCons
  exact loop_correct xs.length xs rfl

/-- Selection sort performs exactly `n * (n - 1) / 2` comparisons on `n` elements. -/
theorem selectionSort_time (xs : List α) :
    (selectionSort xs).time = xs.length * (xs.length - 1) / 2 := by
  unfold selectionSort
  have loop_time : ∀ (fuel : Nat) (ys : List α), ys.length = fuel →
      (selectionSort.loop fuel ys).time = fuel.choose 2 := by
    intro fuel
    induction fuel with
    | zero =>
        intro ys hlen
        cases ys with
        | nil => simp [selectionSort.loop]
        | cons y ys => simp at hlen
    | succ fuel ih =>
        intro ys hlen
        cases ys with
        | nil => simp at hlen
        | cons x xs =>
            have hxlen : xs.length = fuel := by
              simpa only [List.length_cons, Nat.succ.injEq] using hlen
            generalize hresult : (extractMin x xs).ret = result
            rcases result with ⟨minimum, rest⟩
            have hrest : rest.length = fuel := by
              rw [← hxlen, ← extractMin_rest_length x xs, hresult]
            have hrec := ih rest hrest
            simp only [selectionSort.loop, time_bind, time_pure, extractMin_time, hresult, hrec]
            rw [hxlen]
            simpa [Nat.choose_one_right, Nat.add_comm, Nat.succ_eq_add_one] using
              (Nat.choose_succ_succ fuel 1).symm
  rw [← Nat.choose_two_right]
  exact loop_time xs.length xs rfl

end Cslib.Algorithms.Lean.TimeM
