/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.MinMax

import Mathlib.Data.List.Induction

/-!
# Simultaneous minimum and maximum

The paired algorithm from CLRS, fourth edition, Section 9.1, pages 228-229.
One shared comparison orders each fresh pair; its smaller and larger members
then update the saved extrema with one comparison each. Length, parity, list
construction, recursion, and assignments are free in this comparison-count model.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

@[no_expose] private def orderPair {α : Type u} [LinearOrder α] (a b : α) :
    TimeM Nat (α × α) := do
  tick 1
  if a ≤ b then pure (a, b) else pure (b, a)

private theorem orderPair_ret {α : Type u} [LinearOrder α] (a b : α) :
    (orderPair a b).ret = (min a b, max a b) := by
  by_cases hab : a ≤ b
  · simp [orderPair, hab]
  · have hba : b ≤ a := (lt_of_not_ge hab).le
    simp [orderPair, hab, min_eq_right hba, max_eq_left hba]

private theorem orderPair_time {α : Type u} [LinearOrder α] (a b : α) :
    (orderPair a b).time = 1 := by
  by_cases hab : a ≤ b <;> simp [orderPair, hab]

@[no_expose] private def scanPairs {α : Type u} [LinearOrder α] (lo hi : α) :
    List α → TimeM Nat (α × α)
  | [] => pure (lo, hi)
  | [a] => do
      tick 1
      let lo' := if a < lo then a else lo
      tick 1
      let hi' := if hi < a then a else hi
      pure (lo', hi')
  | a :: b :: xs => do
      let pair ← orderPair a b
      tick 1
      let lo' := if pair.1 < lo then pair.1 else lo
      tick 1
      let hi' := if hi < pair.2 then pair.2 else hi
      scanPairs lo' hi' xs

/-- Compute both extrema with a shared comparison for each fresh pair.
Odd inputs seed both extrema with their first element without a comparison;
positive even inputs initialize them by ordering the first pair once. -/
public def minMax {α : Type u} [LinearOrder α] (xs : List α) :
    TimeM Nat (Option (α × α)) :=
  match xs with
  | [] => pure none
  | [a] => pure (some (a, a))
  | a :: b :: rest =>
      if xs.length % 2 = 1 then
        some <$> scanPairs a a (b :: rest)
      else do
        let pair ← orderPair a b
        some <$> scanPairs pair.1 pair.2 rest

private theorem improveMin_eq {α : Type u} [LinearOrder α] (lo a : α) :
    (if a < lo then a else lo) = min lo a := by
  split_ifs with h
  · exact (min_eq_right h.le).symm
  · exact (min_eq_left (le_of_not_gt h)).symm

private theorem improveMax_eq {α : Type u} [LinearOrder α] (hi a : α) :
    (if hi < a then a else hi) = max hi a := by
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (le_of_not_gt h)).symm

private theorem scanPairs_ret {α : Type u} [LinearOrder α] (lo hi : α)
    (xs : List α) :
    (scanPairs lo hi xs).ret = (xs.foldl min lo, xs.foldl max hi) := by
  induction xs using List.twoStepInduction generalizing lo hi with
  | nil => simp [scanPairs]
  | singleton a => simp [scanPairs, improveMin_eq, improveMax_eq]
  | cons_cons a b xs ih _ =>
      simp [scanPairs, orderPair_ret, improveMin_eq, improveMax_eq, ih,
        min_assoc, max_assoc]

private theorem scanPairs_time_even {α : Type u} [LinearOrder α] (lo hi : α)
    (xs : List α) (k : Nat) (hlen : xs.length = 2 * k) :
    (scanPairs lo hi xs).time = 3 * k := by
  induction xs using List.twoStepInduction generalizing lo hi k with
  | nil =>
      have hk : k = 0 := by simp only [List.length_nil] at hlen; omega
      simp [scanPairs, hk]
  | singleton a => simp only [List.length_singleton] at hlen; omega
  | cons_cons a b xs ih _ =>
      have htail : xs.length = 2 * (k - 1) := by
        simp only [List.length_cons] at hlen
        omega
      simp only [scanPairs, time_bind, time_tick, orderPair_time]
      rw [ih _ _ (k - 1) htail]
      simp only [List.length_cons] at hlen
      omega

@[expose] public section

/-- The paired scan returns the canonical minimum and maximum of the original list. -/
theorem minMax_ret {α : Type u} [LinearOrder α] (xs : List α) :
    (minMax xs).ret = xs.min?.bind (fun lo => xs.max?.map (fun hi => (lo, hi))) := by
  cases xs with
  | nil => simp [minMax, List.min?, List.max?]
  | cons a xs =>
      cases xs with
      | nil => simp [minMax, List.min?, List.max?]
      | cons b xs =>
          by_cases h : (xs.length + 1 + 1) % 2 = 1 <;>
            simp [minMax, h, scanPairs_ret, orderPair_ret, List.min?, List.max?]

/-- Empty input is exactly the case without extrema. -/
theorem minMax_eq_none_iff {α : Type u} [LinearOrder α] (xs : List α) :
    (minMax xs).ret = none ↔ xs = [] := by
  rw [minMax_ret]
  cases xs <;> simp [List.min?, List.max?]

/-- Both returned extrema occur in the input and bound all its members. -/
theorem minMax_eq_some_iff {α : Type u} [LinearOrder α] (xs : List α) (lo hi : α) :
    (minMax xs).ret = some (lo, hi) ↔
      lo ∈ xs ∧ hi ∈ xs ∧ (∀ x ∈ xs, lo ≤ x) ∧ (∀ x ∈ xs, x ≤ hi) := by
  rw [minMax_ret]
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact ⟨(List.min?_eq_some_iff.mp ha).1, (List.max?_eq_some_iff.mp hb).1,
      (List.min?_eq_some_iff.mp ha).2, (List.max?_eq_some_iff.mp hb).2⟩
  · rintro ⟨hlo, hhi, hlower, hupper⟩
    exact ⟨lo, List.min?_eq_some_iff.mpr ⟨hlo, hlower⟩,
      hi, List.max?_eq_some_iff.mpr ⟨hhi, hupper⟩, rfl, rfl⟩

/-- Empty input performs no element comparisons. -/
@[simp] theorem minMax_nil {α : Type u} [LinearOrder α] :
    minMax ([] : List α) = pure none := by
  ext <;> simp [minMax]

/-- One element seeds both extrema without comparing elements. -/
@[simp] theorem minMax_singleton {α : Type u} [LinearOrder α] (a : α) :
    minMax [a] = pure (some (a, a)) := by
  ext <;> simp [minMax]

/-- Odd inputs use a free first-element seed and compare each remaining pair three times. -/
theorem minMax_time_odd {α : Type u} [LinearOrder α] (xs : List α) (k : Nat)
    (hlen : xs.length = 2 * k + 1) : (minMax xs).time = 3 * k := by
  cases xs with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons a xs =>
      cases xs with
      | nil =>
          have hk : k = 0 := by simp only [List.length_singleton] at hlen; omega
          simp [hk]
      | cons b xs =>
          have hpar : (xs.length + 1 + 1) % 2 = 1 := by
            simp only [List.length_cons] at hlen
            omega
          have htail : (b :: xs).length = 2 * k := by
            simp only [List.length_cons] at *
            omega
          simp [minMax, hpar, scanPairs_time_even a a (b :: xs) k htail]

/-- Positive even inputs save two comparisons by initializing from one ordered pair. -/
theorem minMax_time_even {α : Type u} [LinearOrder α] (xs : List α) (k : Nat)
    (hlen : xs.length = 2 * k) (hk : 1 ≤ k) : (minMax xs).time = 3 * k - 2 := by
  cases xs with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons a xs =>
      cases xs with
      | nil => simp only [List.length_singleton] at hlen; omega
      | cons b xs =>
          have hpar : ¬(xs.length + 1 + 1) % 2 = 1 := by
            simp only [List.length_cons] at hlen
            omega
          have htail : xs.length = 2 * (k - 1) := by
            simp only [List.length_cons] at hlen
            omega
          simp only [minMax, List.length_cons, hpar, ite_false,
            time_bind, orderPair_time, time_map]
          rw [scanPairs_time_even _ _ xs (k - 1) htail]
          omega

/-- The same run uses exactly `ceil (3 * length / 2) - 2` comparisons when nonempty.
This counts element-order decisions, not full RAM instructions or comparator bit complexity. -/
theorem minMax_time {α : Type u} [LinearOrder α] (xs : List α) :
    (minMax xs).time =
      if xs.length = 0 then 0 else ((3 * xs.length + 1) / 2) - 2 := by
  by_cases hzero : xs.length = 0
  · have hnil : xs = [] := by cases xs <;> simp_all
    simp [hnil]
  · simp only [hzero, ite_false]
    have hdivision := Nat.div_add_mod xs.length 2
    rcases Nat.mod_two_eq_zero_or_one xs.length with heven | hodd
    · have hlen : xs.length = 2 * (xs.length / 2) := by omega
      have hk : 1 ≤ xs.length / 2 := by omega
      rw [minMax_time_even xs (xs.length / 2) hlen hk]
      omega
    · have hlen : xs.length = 2 * (xs.length / 2) + 1 := by omega
      rw [minMax_time_odd xs (xs.length / 2) hlen]
      omega

end

end Cslib.Algorithms.Lean.TimeM
