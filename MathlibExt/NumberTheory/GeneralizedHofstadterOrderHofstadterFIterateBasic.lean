/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedHofstadterOrder
import Mathlib.Order.Monotone.Basic

/-!
# Basic properties of iterated Hofstadter functions

The Hofstadter recurrence gives adjacent increments of zero or one. The iterates retain
this property, and for positive order they are surjective with a collision at `1` and `2`.
-/

namespace MetaMathlibExt

private theorem hofstadterF_le_self (k n : ℕ) : hofstadterF k n ≤ n :=
  hofstadterFAux_le k n n

private theorem hofstadterF_iterate_le_self (k j n : ℕ) : (hofstadterF k)^[j] n ≤ n := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact (hofstadterF_le_self k _).trans ih

private theorem hofstadterF_one (k : ℕ) : hofstadterF k 1 = 1 := by
  have h := hofstadterF_eq k (n := 1) le_rfl
  have h0 := hofstadterF_iterate_le_self k k 0
  change hofstadterF k 1 = 1 - (hofstadterF k)^[k] 0 at h
  omega

private theorem hofstadterF_iterate_one (k j : ℕ) : (hofstadterF k)^[j] 1 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, hofstadterF_one]

private theorem hofstadterF_two (k : ℕ) : hofstadterF k 2 = 1 := by
  rw [hofstadterF_eq k (n := 2) (by decide)]
  change 2 - (hofstadterF k)^[k] 1 = 1
  rw [hofstadterF_iterate_one]

private theorem hofstadterF_diff (k n : ℕ) (hn : 1 ≤ n) :
    (hofstadterF k (n + 1) : ℤ) - hofstadterF k n =
      1 - (((hofstadterF k)^[k] n : ℤ) - (hofstadterF k)^[k] (n - 1)) := by
  have hnext := hofstadterF_eq k (n := n + 1) (by omega)
  rw [Nat.add_sub_cancel] at hnext
  have hprev := hofstadterF_eq k hn
  have hle := hofstadterF_iterate_le_self k k n
  have hle' := hofstadterF_iterate_le_self k k (n - 1)
  omega

-- The next application of `hofstadterF k` only needs a step at a smaller or equal input.
private theorem hofstadterF_iterate_step_below (k N : ℕ)
    (hstep : ∀ m < N, hofstadterF k (m + 1) = hofstadterF k m ∨
      hofstadterF k (m + 1) = hofstadterF k m + 1)
    (j n : ℕ) (hn : n < N) : (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n ∨
      (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n + 1 := by
  induction j with
  | zero => exact Or.inr rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rcases ih with h | h
    · exact Or.inl (congrArg (hofstadterF k) h)
    · rw [h]
      exact hstep _ ((hofstadterF_iterate_le_self k j n).trans_lt hn)

private theorem hofstadterF_step (k n : ℕ) :
    hofstadterF k (n + 1) = hofstadterF k n ∨ hofstadterF k (n + 1) = hofstadterF k n + 1 := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero => exact Or.inr (by rw [hofstadterF_zero, hofstadterF_one])
  | succ n =>
    have hdiff := hofstadterF_diff k (n + 1) (by omega)
    rw [Nat.add_sub_cancel] at hdiff
    rcases hofstadterF_iterate_step_below k (n + 1) ih k n (Nat.lt_succ_self n) with h | h
    · right
      rw [h] at hdiff
      omega
    · left
      rw [h] at hdiff
      omega

private theorem hofstadterF_iterate_step (k j n : ℕ) :
    (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n ∨
      (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n + 1 :=
  hofstadterF_iterate_step_below k (n + 1) (fun m _ => hofstadterF_step k m) j n
    (Nat.lt_succ_self n)

private theorem hofstadterF_iterate_monotone (k j : ℕ) : Monotone (hofstadterF k)^[j] := by
  apply monotone_nat_of_le_succ
  intro n
  rcases hofstadterF_iterate_step k j n with h | h <;> omega

private theorem hofstadterF_lt_self (k n : ℕ) (hn : 2 ≤ n) : hofstadterF k n < n := by
  have h := hofstadterF_eq k (n := n) (by omega)
  have hpos := hofstadterF_iterate_monotone k k (show 1 ≤ n - 1 by omega)
  rw [hofstadterF_iterate_one] at hpos
  omega

private theorem hofstadterF_surjective (k : ℕ) (hk : 1 ≤ k) :
    Function.Surjective (hofstadterF k) := by
  -- The unit-step property ensures that no value below a reached value is skipped.
  have reach (n : ℕ) : ∀ y ≤ hofstadterF k n, ∃ m, hofstadterF k m = y := by
    induction n with
    | zero =>
      intro y hy
      rw [hofstadterF_zero] at hy
      exact ⟨0, (hofstadterF_zero k).trans (Nat.le_zero.mp hy).symm⟩
    | succ n ih =>
      intro y hy
      by_cases hle : y ≤ hofstadterF k n
      · exact ih y hle
      · refine ⟨n + 1, ?_⟩
        rcases hofstadterF_step k n with h | h <;> omega
  intro y
  -- A positive iterate is bounded by its first application, so the recurrence gives
  -- `2 * y + 1 ≤ F (2 * y + 1) + F (2 * y)`.
  have hle : (hofstadterF k)^[k] (y + y) ≤ hofstadterF k (y + y) := by
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    rw [hi, Function.iterate_succ_apply]
    exact hofstadterF_iterate_le_self (i + 1) i _
  have hrec := hofstadterF_eq k (n := y + y + 1) (by omega)
  rw [Nat.add_sub_cancel] at hrec
  apply reach (y + y + 1) y
  rcases hofstadterF_step k (y + y) with h | h <;> omega

@[expose] public section

/-- **Basic properties of the iterated Hofstadter functions.** Let $j, k \ge 1$, let $F_k$ be the
generalized Hofstadter function, and write $F_k^i$ for its $i$-fold iterate. Then
$F_k^j(1) = F_k^j(2) = 1$; $F_k^j(n) \ge 1$ for every $n \ge 1$; $F_k^j(n) < n$ for every
$n \ge 2$; $F_k(n+1) - F_k(n) = 1 - \bigl(F_k^k(n) - F_k^k(n-1)\bigr)$ in $\mathbb{Z}$ for every
$n \ge 1$; $F_k^j(n+1)$ equals $F_k^j(n)$ or $F_k^j(n) + 1$ for every $n \ge 0$; and $F_k^j$ is
monotone and surjective from $\mathbb{N}$ to $\mathbb{N}$ but not injective.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 2 (`jis-2026-26.3.3-prop-2`). -/
public theorem hofstadterF_iterate_basic {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (hofstadterF k)^[j] 1 = 1 ∧ (hofstadterF k)^[j] 2 = 1 ∧
      (∀ n, 1 ≤ n → 1 ≤ (hofstadterF k)^[j] n) ∧
      (∀ n, 2 ≤ n → (hofstadterF k)^[j] n < n) ∧
      (∀ n, 1 ≤ n →
        (hofstadterF k (n + 1) : ℤ) - hofstadterF k n =
          1 - (((hofstadterF k)^[k] n : ℤ) - (hofstadterF k)^[k] (n - 1))) ∧
      (∀ n, (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n ∨
        (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n + 1) ∧
      Monotone (hofstadterF k)^[j] ∧ Function.Surjective (hofstadterF k)^[j] ∧
      ¬ Function.Injective (hofstadterF k)^[j] := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  have hone := hofstadterF_iterate_one k (i + 1)
  have htwo : (hofstadterF k)^[i + 1] 2 = 1 := by
    rw [Function.iterate_succ_apply, hofstadterF_two, hofstadterF_iterate_one]
  have hmono := hofstadterF_iterate_monotone k (i + 1)
  refine ⟨hone, htwo, ?_, ?_, hofstadterF_diff k, hofstadterF_iterate_step k (i + 1),
    hmono, (hofstadterF_surjective k hk).iterate (i + 1), ?_⟩
  · intro n hn
    simpa only [hone] using hmono hn
  · intro n hn
    rw [Function.iterate_succ_apply]
    exact (hofstadterF_iterate_le_self k i _).trans_lt (hofstadterF_lt_self k n hn)
  · intro hinj
    exact (by decide : (1 : ℕ) ≠ 2) (hinj (hone.trans htwo.symm))

end

end MetaMathlibExt
