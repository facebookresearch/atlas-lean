/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Randomized quicksort: expected comparisons

The expected-comparison recurrence `E (n+1) = n + (2/(n+1)) *
sum_{k <= n} E k` has closed form `2 (n+2) H (n+1) - 4 (n+1)`,
hence `E n <= 2 n H n`. (An earlier draft of the closed form,
`2 (n+1) (H (n+1) - 1)`, was refuted at `n = 1` during this work:
`E 2 = 1`.) This is roadmap package ALG-10a of the Atlas TCS
canon roadmap.

Source: CLRS (4th ed.), Section 7.3.
-/

open Finset

/-- Harmonic numbers `H n = ∑_{k=1}^n 1 / k` (as `∑ k ∈ range n,
1 / (k + 1)`). -/
noncomputable def harmonicN (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, 1 / (k + 1 : ℝ)

/-- The randomized-quicksort expected-comparison recurrence:
`E 0 = 0` and `E (n + 1) = n + (2 / (n + 1)) * ∑_{k ≤ n} E k`
(the pivot is uniform, and after splitting, the two subproblems
have sizes `k` and `n - k`; summing the recurrence solution
against the pair-count identity gives the closed form below). -/
noncomputable def qsPair : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | (n + 1) =>
      let e := (n : ℝ) + (2 / (n + 1 : ℝ)) * (qsPair n).2
      (e, (qsPair n).2 + e)

/-- Expected number of comparisons of randomized quicksort on
`n` distinct keys, defined through `qsPair` (whose second
component is the running sum `∑_{k ≤ n} qsExpected k`). -/
noncomputable def qsExpected (n : ℕ) : ℝ := (qsPair n).1

private theorem harmonicN_succ (n : ℕ) :
    harmonicN (n + 1) = harmonicN n + 1 / ((n : ℝ) + 1) := by
  simp [harmonicN, Finset.sum_range_succ]

private theorem harmonicN_nonneg (n : ℕ) : 0 ≤ harmonicN n := by
  apply Finset.sum_nonneg
  intro k _
  positivity

private theorem harmonicN_le (n : ℕ) : harmonicN n ≤ (n : ℝ) := by
  unfold harmonicN
  have h : ∀ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
    intro k _
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith
    rw [div_le_one hpos]
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith
  calc ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1)
      ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum h
    _ = ((Finset.range n).card : ℝ) * 1 := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = (n : ℝ) := by simp [Finset.card_range]

private theorem qsPair_eq (n : ℕ) :
    qsPair n = (2 * ((n : ℝ) + 1) * harmonicN n - 4 * (n : ℝ),
                ((n : ℝ) + 1) * ((n : ℝ) + 2) * harmonicN (n + 1)
                  - ((n : ℝ) + 1) * (5 * (n : ℝ) + 4) / 2) := by
  induction n with
  | zero =>
    simp [qsPair, harmonicN]
    ring
  | succ n ih =>
    simp only [qsPair, ih]
    apply Prod.ext
    · simp only
      push_cast
      have h1 : ((n : ℝ) + 1) ≠ 0 := by
        have hk := Nat.cast_nonneg (α := ℝ) n
        linarith
      field_simp
      ring
    · simp only
      push_cast
      have h1 : ((n : ℝ) + 1) ≠ 0 := by
        have hk := Nat.cast_nonneg (α := ℝ) n
        linarith
      have h2 : ((n : ℝ) + 2) ≠ 0 := by
        have hk := Nat.cast_nonneg (α := ℝ) n
        linarith
      have hH : harmonicN (n + 1 + 1) = harmonicN (n + 1) + 1 / ((n : ℝ) + 2) := by
        have h := harmonicN_succ (n + 1)
        push_cast at h
        have h2eq : ((n : ℝ) + 1 + 1) = ((n : ℝ) + 2) := by ring
        rw [h2eq] at h
        exact h
      rw [hH]
      field_simp
      ring

private theorem qsExpected_form (n : ℕ) :
    qsExpected n = 2 * ((n : ℝ) + 1) * harmonicN n - 4 * (n : ℝ) := by
  simp [qsExpected, qsPair_eq]

/-- Expected comparisons of randomized quicksort are at most
`2 n H n`. -/
theorem qsExpected_le (n : ℕ) : qsExpected n ≤ 2 * n * harmonicN n := by
  cases n with
  | zero =>
    simp [qsExpected, qsPair]
  | succ n =>
    have h := qsExpected_form (n + 1)
    rw [h]
    push_cast
    have hHle : harmonicN (n + 1) ≤ ((n : ℝ) + 1) := by
      have hle := harmonicN_le (n + 1)
      push_cast at hle
      exact hle
    have hHnonneg : 0 ≤ harmonicN (n + 1) := harmonicN_nonneg _
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [hHle, hHnonneg, hnnonneg]

/-- The pair-count identity behind the bound: closed form
`qsExpected (n + 1) = 2 * (n + 2) * harmonicN (n + 1) - 4 * (n + 1)`
(the exact expected number of comparisons is
`2 (n+2) H (n+1) - 4 (n+1)`, i.e. `2 (n+1) H n - 4 n`). -/
theorem qsExpected_eq (n : ℕ) :
    qsExpected (n + 1) = 2 * (n + 2) * harmonicN (n + 1) - 4 * (n + 1) := by
  have h := qsExpected_form (n + 1)
  rw [h]
  push_cast
  ring
