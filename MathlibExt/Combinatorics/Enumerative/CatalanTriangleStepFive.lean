/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step-five sums of Catalan's triangle

The differences between two pairs of column sums in each row give consecutive Fibonacci numbers.
-/

namespace MetaMathlibExt

namespace catalanTriangle_stepFive_sub_eq_fib

/-- Adjacent differences in an odd row of Pascal's triangle. Column zero is the
difference of the two equal middle coefficients, so Catalan's triangle starts at column one. -/
private def diff (n k : ℕ) : ℚ :=
  ((2 * n + 1).choose (n + k) : ℚ) - (2 * n + 1).choose (n + k + 1)

private theorem diff_zero (n : ℕ) : diff n 0 = 0 := by
  simp [diff, Nat.choose_symm_half]

private theorem diff_of_lt {n k : ℕ} (h : n + 1 < k) : diff n k = 0 := by
  simp [diff, Nat.choose_eq_zero_of_lt (show 2 * n + 1 < n + k by omega),
    Nat.choose_eq_zero_of_lt (show 2 * n + 1 < n + k + 1 by omega)]

private theorem entry_eq_diff (n k : ℕ) :
    (if k ≤ n then (k + 1 : ℚ) / (n + 1) * ((2 * (n + 1)).choose (n - k) : ℚ) else 0) =
      diff n (k + 1) := by
  split_ifs with hk
  · have hsymm := Nat.choose_symm_of_eq_add
        (show 2 * (n + 1) = (n - k) + (n + k + 2) by omega)
    rw [hsymm, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Nat.choose_succ_succ' (2 * n + 1) (n + k + 1)]
    have h := Nat.choose_succ_right_eq (2 * n + 1) (n + k + 1)
    rw [show 2 * n + 1 - (n + k + 1) = n - k by omega] at h
    have hq := congrArg (Nat.cast : ℕ → ℚ) h
    push_cast [Nat.cast_sub hk] at hq
    simp only [diff, ← Nat.add_assoc, Nat.cast_add]
    field_simp
    linarith
  · exact (diff_of_lt (by omega)).symm

-- Two applications of Pascal's rule advance to the next odd row.
private theorem diff_succ (n k : ℕ) :
    diff (n + 1) (k + 1) = diff n k + 2 * diff n (k + 1) + diff n (k + 2) := by
  simp only [diff, show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
    show n + 1 + (k + 1) = (n + k) + 1 + 1 by omega, ← Nat.add_assoc,
    Nat.choose_succ_succ', Nat.cast_add]
  ring

private def evenTerm (n j : ℕ) : ℚ := diff n (5 * j + 2) - diff n (5 * j + 3)

private def oddTerm (n j : ℕ) : ℚ := diff n (5 * j + 1) - diff n (5 * j + 4)

private theorem evenTerm_succ (n j : ℕ) :
    evenTerm (n + 1) j = evenTerm n j + oddTerm n j := by
  unfold evenTerm oddTerm
  rw [diff_succ n (5 * j + 1), diff_succ n (5 * j + 2)]
  ring

private theorem oddTerm_succ (n j : ℕ) :
    oddTerm (n + 1) j = evenTerm n j + 2 * oddTerm n j +
      (diff n (5 * j) - diff n (5 * (j + 1))) := by
  unfold evenTerm oddTerm
  rw [diff_succ n (5 * j), diff_succ n (5 * j + 3), Nat.mul_add, Nat.mul_one]
  ring

-- Take the same number of blocks in both rows. The extra terms vanish outside the triangle.
private theorem step_sums (n m : ℕ) (hm : n ≤ m) :
    (∑ j ∈ Finset.range (m + 1), evenTerm n j) = Nat.fib (2 * n) ∧
      (∑ j ∈ Finset.range (m + 1), oddTerm n j) = Nat.fib (2 * n + 1) := by
  induction n with
  | zero =>
    have he (j : ℕ) : evenTerm 0 j = 0 := by
      simp [evenTerm, diff_of_lt (show 0 + 1 < 5 * j + 2 by omega),
        diff_of_lt (show 0 + 1 < 5 * j + 3 by omega)]
    have ho (j : ℕ) : oddTerm 0 (j + 1) = 0 := by
      simp [oddTerm, diff_of_lt (show 0 + 1 < 5 * (j + 1) + 1 by omega),
        diff_of_lt (show 0 + 1 < 5 * (j + 1) + 4 by omega)]
    have h₀ : oddTerm 0 0 = 1 := by
      norm_num [oddTerm, diff, Nat.choose]
    simp [he, Finset.sum_range_succ', ho, h₀]
  | succ n ih =>
    obtain ⟨he, ho⟩ := ih (by omega)
    have htel : (∑ j ∈ Finset.range (m + 1),
        (diff n (5 * j) - diff n (5 * (j + 1)))) = 0 := by
      rw [Finset.sum_range_sub' (fun j => diff n (5 * j))]
      simp [diff_zero, diff_of_lt (show n + 1 < 5 * (m + 1) by omega)]
    simp only [evenTerm_succ, oddTerm_succ, Finset.sum_add_distrib, ← Finset.mul_sum, htel,
      he, ho]
    simp only [Nat.mul_succ, Nat.fib_add_two, Nat.cast_add, true_and]
    ring

end catalanTriangle_stepFive_sub_eq_fib

open catalanTriangle_stepFive_sub_eq_fib

/-- **Alternating step-five sums of Catalan's triangle are Fibonacci numbers.** For natural
numbers $n$ and $k$ let $d(n, k) = \frac{k + 1}{n + 1} \binom{2(n + 1)}{n - k}$ if $k \le n$,
and $d(n, k) = 0$ if $k > n$. Let $F_m$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then
for every $n \in \mathbb{N}$,
$\sum_{j=0}^{n} \bigl(d(n, 5j + 1) - d(n, 5j + 2)\bigr) = F_{2n}$ and
$\sum_{j=0}^{n} \bigl(d(n, 5j) - d(n, 5j + 3)\bigr) = F_{2n+1}$.

The numbers $d(n, k)$ form Catalan's triangle (OEIS A039598), the Riordan array $(g, xg)$ with
$g(x) = (1 - 2x - \sqrt{1 - 4x})/(2x^2)$; since $d(n, m) = 0$ for $m > n$, the sums are the full
sums over all $j \ge 0$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4,
Proposition 13. -/
public theorem catalanTriangle_stepFive_sub_eq_fib (n : ℕ) :
    let d : ℕ → ℕ → ℚ := fun n k =>
      if k ≤ n then (k + 1 : ℚ) / (n + 1) * ((2 * (n + 1)).choose (n - k) : ℚ) else 0
    ∑ j ∈ Finset.range (n + 1), (d n (5 * j + 1) - d n (5 * j + 2)) = Nat.fib (2 * n) ∧
      ∑ j ∈ Finset.range (n + 1), (d n (5 * j) - d n (5 * j + 3)) = Nat.fib (2 * n + 1) := by
  simpa only [entry_eq_diff, evenTerm, oddTerm] using step_sums n n le_rfl

end MetaMathlibExt
