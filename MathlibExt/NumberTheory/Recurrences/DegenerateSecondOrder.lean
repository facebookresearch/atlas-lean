/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Ring

/-!
# Closed forms of eight degenerate second-order recurrences

The first four formulas describe repeating blocks of two, four, six, and three terms.
The next two give affine and alternating affine formulas in the index. The last two describe
constant and alternating tails starting at index one.
-/

namespace MetaMathlibExt

namespace degenerate_secondOrder_closedForms

private theorem periodic_mul_add_eq {w : ℕ → ℤ} {p : ℕ} (hp : Function.Periodic w p) (n r : ℕ) :
    w (p * n + r) = w r := by
  simpa only [Nat.cast_id, Nat.mul_comm n p, Nat.add_comm r] using hp.nat_mul n r

/-- A sequence satisfying `w (k + 2) = w k` repeats its first two terms. -/
public theorem period_two (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = w k) (n : ℕ) :
    w (2 * n) = w 0 ∧ w (2 * n + 1) = w 1 := by
  have h := periodic_mul_add_eq (p := 2) hw n
  exact ⟨h 0, h 1⟩

/-- Negating the term two steps back gives a four-term cycle. -/
public theorem period_four (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = -w k) (n : ℕ) :
    w (4 * n) = w 0 ∧ w (4 * n + 1) = w 1 ∧ w (4 * n + 2) = -w 0 ∧
      w (4 * n + 3) = -w 1 := by
  have anti : Function.Antiperiodic w 2 := hw
  have h := periodic_mul_add_eq (p := 4) anti.periodic_two_mul n
  exact ⟨h 0, h 1, (h 2).trans (hw 0), (h 3).trans (hw 1)⟩

/-- Taking the difference of the preceding two terms gives a six-term cycle. -/
public theorem period_six (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = w (k + 1) - w k) (n : ℕ) :
    w (6 * n) = w 0 ∧ w (6 * n + 1) = w 1 ∧ w (6 * n + 2) = w 1 - w 0 ∧
      w (6 * n + 3) = -w 0 ∧ w (6 * n + 4) = -w 1 ∧ w (6 * n + 5) = w 0 - w 1 := by
  have anti : Function.Antiperiodic w 3 := by
    intro k
    rw [hw (k + 1), hw k]
    omega
  have h := periodic_mul_add_eq (p := 6) anti.periodic_two_mul n
  refine ⟨h 0, h 1, (h 2).trans (hw 0), (h 3).trans (anti 0), (h 4).trans (anti 1), ?_⟩
  rw [h 5, anti 2, hw 0, neg_sub]

/-- Negating the sum of the preceding two terms gives a three-term cycle. -/
public theorem period_three (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = -w (k + 1) - w k) (n : ℕ) :
    w (3 * n) = w 0 ∧ w (3 * n + 1) = w 1 ∧ w (3 * n + 2) = -w 1 - w 0 := by
  have per : Function.Periodic w 3 := by
    intro k
    rw [hw (k + 1), hw k]
    omega
  have h := periodic_mul_add_eq per n
  exact ⟨h 0, h 1, (h 2).trans (hw 0)⟩

/-- A sequence with zero second differences is affine in its index. -/
public theorem affine (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = 2 * w (k + 1) - w k) (n : ℕ) :
    w n = n * w 1 - ((n : ℤ) - 1) * w 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
    rw [hw, ih₁, ih₀]
    push_cast
    ring

/-- A sequence with repeated characteristic root `-1` has an alternating affine formula. -/
public theorem alternating_affine (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = -2 * w (k + 1) - w k)
    (n : ℕ) : w n = (-1) ^ (n + 1) * (n * w 1 + ((n : ℤ) - 1) * w 0) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
    rw [hw, ih₁, ih₀]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_add, pow_one]
    ring

/-- Copying the preceding term gives a constant tail from index one. -/
public theorem constant_tail (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = w (k + 1))
    (n : ℕ) (hn : 1 ≤ n) : w n = w 1 := by
  obtain _ | n := n
  · omega
  · clear hn
    induction n with
    | zero => rfl
    | succ n ih => exact (hw n).trans ih

/-- Negating the preceding term gives an alternating tail from index one. -/
public theorem alternating_tail (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = -w (k + 1))
    (n : ℕ) (hn : 1 ≤ n) : w n = (-1) ^ (n + 1) * w 1 := by
  obtain _ | n := n
  · omega
  · clear hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hw n, ih]
      simp [pow_succ]

end degenerate_secondOrder_closedForms

/-- **Closed forms of eight degenerate second-order recurrences.** For every integer sequence
$(w_j)_{j \ge 0}$ and every $n \in \mathbb{N}$: if $w_{j+2} = w_j$ for all $j$, then
$w_{2n} = w_0$ and $w_{2n+1} = w_1$; if $w_{j+2} = -w_j$ for all $j$, then $w_{4n} = w_0$,
$w_{4n+1} = w_1$, $w_{4n+2} = -w_0$ and $w_{4n+3} = -w_1$; if $w_{j+2} = w_{j+1} - w_j$ for all
$j$, then $w_{6n} = w_0$, $w_{6n+1} = w_1$, $w_{6n+2} = w_1 - w_0$, $w_{6n+3} = -w_0$,
$w_{6n+4} = -w_1$ and $w_{6n+5} = w_0 - w_1$; if $w_{j+2} = -w_{j+1} - w_j$ for all $j$, then
$w_{3n} = w_0$, $w_{3n+1} = w_1$ and $w_{3n+2} = -w_1 - w_0$; if $w_{j+2} = 2 w_{j+1} - w_j$ for
all $j$, then $w_n = n w_1 - (n - 1) w_0$; if $w_{j+2} = -2 w_{j+1} - w_j$ for all $j$, then
$w_n = (-1)^{n+1} (n w_1 + (n - 1) w_0)$; if $w_{j+2} = w_{j+1}$ for all $j$ and $n \ge 1$, then
$w_n = w_1$; and if $w_{j+2} = -w_{j+1}$ for all $j$ and $n \ge 1$, then $w_n = (-1)^{n+1} w_1$.

In the paper's notation $W_{j+2} = a W_{j+1} + b W_j$ these are the pairs $(a, b) = (0, 1)$,
$(0, -1)$, $(1, -1)$, $(-1, -1)$, $(2, -1)$, $(-2, -1)$, $(1, 0)$ and $(-1, 0)$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.3
(`integers-2024-A36-thm-1-3`). -/
public theorem degenerate_secondOrder_closedForms :
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = w k) →
      ∀ n, w (2 * n) = w 0 ∧ w (2 * n + 1) = w 1) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w k) →
      ∀ n, w (4 * n) = w 0 ∧ w (4 * n + 1) = w 1 ∧ w (4 * n + 2) = -w 0 ∧
        w (4 * n + 3) = -w 1) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = w (k + 1) - w k) →
      ∀ n, w (6 * n) = w 0 ∧ w (6 * n + 1) = w 1 ∧ w (6 * n + 2) = w 1 - w 0 ∧
        w (6 * n + 3) = -w 0 ∧ w (6 * n + 4) = -w 1 ∧ w (6 * n + 5) = w 0 - w 1) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w (k + 1) - w k) →
      ∀ n, w (3 * n) = w 0 ∧ w (3 * n + 1) = w 1 ∧ w (3 * n + 2) = -w 1 - w 0) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = 2 * w (k + 1) - w k) →
      ∀ n : ℕ, w n = n * w 1 - ((n : ℤ) - 1) * w 0) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -2 * w (k + 1) - w k) →
      ∀ n : ℕ, w n = (-1) ^ (n + 1) * (n * w 1 + ((n : ℤ) - 1) * w 0)) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = w (k + 1)) → ∀ n, 1 ≤ n → w n = w 1) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w (k + 1)) →
      ∀ n, 1 ≤ n → w n = (-1) ^ (n + 1) * w 1) :=
  open degenerate_secondOrder_closedForms in
  ⟨period_two, period_four, period_six, period_three, affine, alternating_affine,
    constant_tail, alternating_tail⟩

end MetaMathlibExt
