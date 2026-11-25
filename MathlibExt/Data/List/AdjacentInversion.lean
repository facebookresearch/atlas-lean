/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Pairwise
public import Mathlib.Order.Monotone.Basic

/-!
# Termination of adjacent inversion reduction

A word over an arbitrary linearly ordered type has finitely many inversions.
The natural-number weight below strictly decreases both on swapping an
adjacent inverted pair and on replacing that pair by a single letter. No
well-ordering or finiteness assumption on the alphabet is used.
-/

@[expose] public section

namespace List

universe v

variable {I : Type v} [LinearOrder I]

/-- The number of strictly inverted pairs in a word. -/
def inversionCount : List I → ℕ
  | [] => 0
  | i :: xs => xs.countP (fun j => decide (j < i)) + inversionCount xs

/-- Search from the left for an actual adjacent inversion. The returned
data records its original prefix and suffix. -/
def adjacentInversion : List I → Option (List I × I × I × List I)
  | [] => none
  | [_] => none
  | i :: j :: xs =>
      if j < i then some ([], i, j, xs)
      else (adjacentInversion (j :: xs)).map
        (fun (p, a, b, s) => (i :: p, a, b, s))

/-- The search returns only genuine decompositions with an inverted pair. -/
theorem adjacentInversion_spec (xs : List I) (p : List I) (i j : I) (s : List I)
    (h : adjacentInversion xs = some (p, i, j, s)) :
    xs = p ++ i :: j :: s ∧ j < i := by
  induction xs generalizing p i j s with
  | nil => simp only [adjacentInversion, reduceCtorEq] at h
  | cons a xs ih =>
      cases xs with
      | nil => simp only [adjacentInversion, reduceCtorEq] at h
      | cons b xs =>
          by_cases hba : b < a
          · simp only [adjacentInversion, hba, ↓reduceIte] at h
            have ht : ([], a, b, xs) = (p, i, j, s) := Option.some.inj h
            cases ht
            exact ⟨rfl, hba⟩
          · simp only [adjacentInversion, hba, ↓reduceIte] at h
            cases hr : adjacentInversion (b :: xs) with
            | none => simp only [hr, Option.map_none, reduceCtorEq] at h
            | some t =>
                rcases t with ⟨q, c, d, ys⟩
                simp only [hr, Option.map_some] at h
                have ht : (a :: q, c, d, ys) = (p, i, j, s) := Option.some.inj h
                cases ht
                obtain ⟨hxs, hdc⟩ := ih q i j s hr
                refine ⟨?_, hdc⟩
                rw [hxs]
                rfl

/-- A word with no adjacent inversion is weakly increasing. -/
theorem pairwise_le_of_adjacentInversion_eq_none (xs : List I)
    (h : adjacentInversion xs = none) : xs.Pairwise (· ≤ ·) := by
  induction xs with
  | nil => exact Pairwise.nil
  | cons a xs ih =>
      cases xs with
      | nil => simp only [pairwise_singleton]
      | cons b xs =>
          by_cases hba : b < a
          · simp only [adjacentInversion, hba, ↓reduceIte, reduceCtorEq] at h
          · have hr : adjacentInversion (b :: xs) = none := by
              cases hs : adjacentInversion (b :: xs) with
              | none => rfl
              | some t =>
                  simp only [adjacentInversion, hba, ↓reduceIte, hs,
                    Option.map_some, reduceCtorEq] at h
            have htail : (b :: xs).Pairwise (· ≤ ·) := ih hr
            rw [pairwise_cons]
            refine ⟨?_, htail⟩
            intro c hc
            rcases mem_cons.mp hc with rfl | hc
            · exact le_of_not_gt hba
            · exact (le_of_not_gt hba).trans ((pairwise_cons.mp htail).1 c hc)

/-- Weakly increasing words are fixed by the adjacent-inversion search. -/
theorem adjacentInversion_eq_none_of_pairwise_le (xs : List I)
    (h : xs.Pairwise (· ≤ ·)) : adjacentInversion xs = none := by
  cases hr : adjacentInversion xs with
  | none => rfl
  | some t =>
      rcases t with ⟨p, i, j, s⟩
      obtain ⟨rfl, hji⟩ := adjacentInversion_spec xs p i j s hr
      have htail : (i :: j :: s).Pairwise (· ≤ ·) := (pairwise_append.mp h).2.1
      have hij : i ≤ j := (pairwise_cons.mp htail).1 j mem_cons_self
      exact (not_lt_of_ge hij hji).elim

omit [LinearOrder I] in
private theorem countP_adjacent_swap (q : I → Bool)
    (p : List I) (i j : I) (s : List I) :
    (p ++ i :: j :: s).countP q = (p ++ j :: i :: s).countP q := by
  simp only [countP_append, countP_cons]
  omega

/-- An adjacent inverted pair contributes exactly the removed inversion. -/
theorem inversionCount_adjacent_swap (p : List I) (i j : I) (s : List I)
    (hji : j < i) :
    inversionCount (p ++ j :: i :: s) + 1 = inversionCount (p ++ i :: j :: s) := by
  induction p with
  | nil =>
      simp [inversionCount, hji, not_lt_of_gt hji] <;> omega
  | cons a p ih =>
      have hc := countP_adjacent_swap (fun b : I => decide (b < a)) p i j s
      simp only [cons_append, inversionCount]
      omega

/-- A uniform finite bound for the inversion count of each word. -/
theorem inversionCount_le_length_sq (xs : List I) :
    inversionCount xs ≤ xs.length * xs.length := by
  induction xs with
  | nil => exact le_rfl
  | cons i xs ih =>
      have hc : xs.countP (fun j => decide (j < i)) ≤ xs.length := countP_le_length ..
      simp only [inversionCount, length_cons]
      calc
        xs.countP (fun j => decide (j < i)) + inversionCount xs ≤
            xs.length + xs.length * xs.length := Nat.add_le_add hc ih
        _ ≤ (xs.length + 1) * (xs.length + 1) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
          omega

/-- The start of the block of weights assigned to words of a given length. -/
def inversionOffset : ℕ → ℕ
  | 0 => 0
  | n + 1 => inversionOffset n + n * n + 1

/-- A single natural-number termination measure for reduction of words. -/
def inversionWeight (xs : List I) : ℕ :=
  inversionOffset xs.length + inversionCount xs

theorem inversionOffset_mono : Monotone inversionOffset := by
  apply monotone_nat_of_le_succ
  intro n
  rw [inversionOffset]
  omega

/-- Every word of shorter length has lower weight, independently of its
letters. This applies to all terms of an overlapping bracket contraction. -/
theorem inversionWeight_lt_of_length_lt {xs ys : List I}
    (h : xs.length < ys.length) : inversionWeight xs < inversionWeight ys := by
  have hi := inversionCount_le_length_sq xs
  have ho := inversionOffset_mono (show xs.length + 1 ≤ ys.length by omega)
  rw [inversionOffset] at ho
  unfold inversionWeight
  omega

theorem inversionWeight_adjacent_swap_lt (p : List I) (i j : I) (s : List I)
    (hji : j < i) :
    inversionWeight (p ++ j :: i :: s) < inversionWeight (p ++ i :: j :: s) := by
  have hi := inversionCount_adjacent_swap p i j s hji
  have hl : (p ++ j :: i :: s).length = (p ++ i :: j :: s).length := by
    simp only [length_append, length_cons]
  unfold inversionWeight
  rw [hl]
  omega

/-- Replacing two adjacent letters by any single letter decreases the weight,
regardless of the number of inversions of the resulting word. -/
theorem inversionWeight_contract_lt (p : List I) (i j k : I) (s : List I) :
    inversionWeight (p ++ k :: s) < inversionWeight (p ++ i :: j :: s) := by
  have hl : (p ++ i :: j :: s).length = (p ++ k :: s).length + 1 := by
    simp only [length_append, length_cons]
    omega
  have hi := inversionCount_le_length_sq (p ++ k :: s)
  unfold inversionWeight
  rw [hl, inversionOffset]
  omega

end List
