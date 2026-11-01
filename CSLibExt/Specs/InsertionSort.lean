/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Specs.Sorting

@[expose] public section

namespace CSLibExt.Specs.Sorting

/-!
# Insertion sort (Weeks 3-4 core, 90-day plan #2 SPECS)

The first verified algorithm against `SortingSpec`: insertion sort,
proved (not just stated) to return a sorted permutation. Core Lean
only, so the proof uses `List.Perm` / `List.Pairwise` directly.

This is the template for later verified algorithms: one implementation,
one relational spec, one proof. Quicksort / mergesort come later and
must satisfy the same `SortingSpec`, never a private variant.
-/

/-- Insert `x` into a sorted list, keeping it sorted. -/
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

/-- Insertion sort. -/
def isort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (isort xs)

/-- Membership of the inserted list: only `x` is new. -/
theorem mem_insert {x z : Nat} {xs : List Nat} (h : z ∈ insert x xs) :
    z = x ∨ z ∈ xs := by
  induction xs with
  | nil =>
      rw [show insert x [] = [x] from rfl] at h
      exact Or.inl (List.mem_singleton.mp h)
  | cons y ys ih =>
      simp only [insert] at h
      split at h
      · simp only [List.mem_cons] at h
        cases h with
        | inl hz => exact Or.inl hz
        | inr h2 =>
            cases h2 with
            | inl hy =>
                subst hy; exact Or.inr List.mem_cons_self
            | inr h3 => exact Or.inr (List.mem_cons_of_mem _ h3)
      · simp only [List.mem_cons] at h
        cases h with
        | inl hy =>
            subst hy; exact Or.inr List.mem_cons_self
        | inr h2 =>
            cases ih h2 with
            | inl hz => exact Or.inl hz
            | inr hz => exact Or.inr (List.mem_cons_of_mem _ hz)

/-- Insertion preserves the multiset: `insert x xs` is a permutation
of `x :: xs`. -/
theorem perm_insert (x : Nat) (xs : List Nat) :
    List.Perm (insert x xs) (x :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
      simp only [insert]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

/-- Insertion preserves sortedness. -/
theorem sorted_insert {x : Nat} {xs : List Nat} (h : SortedProp xs) :
    SortedProp (insert x xs) := by
  induction xs with
  | nil => exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons y ys ih =>
      simp only [insert]
      split
      · rename_i hle
        cases h with
        | cons hhead htail =>
            apply List.Pairwise.cons
            · intro z hz
              simp only [List.mem_cons] at hz
              cases hz with
              | inl h_eq => rw [h_eq]; exact hle
              | inr h_mem => exact Nat.le_trans hle (hhead z h_mem)
            · exact List.Pairwise.cons hhead htail
      · rename_i hnot
        have hlt : y < x := Nat.not_le.mp hnot
        cases h with
        | cons hhead htail =>
            apply List.Pairwise.cons
            · intro z hz
              cases mem_insert hz with
              | inl h_eq => rw [h_eq]; exact Nat.le_of_lt hlt
              | inr h_mem => exact hhead z h_mem
            · exact ih htail

/-- Insertion sort returns a sorted permutation (the spec). -/
theorem sorting_isort (xs : List Nat) : SortingSpec xs (isort xs) := by
  induction xs with
  | nil => exact ⟨List.Perm.refl _, List.Pairwise.nil⟩
  | cons x xs ih =>
      refine ⟨?_, sorted_insert ih.2⟩
      exact (perm_insert x (isort xs)).trans (List.Perm.cons x ih.1)

end CSLibExt.Specs.Sorting
