/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite window criterion for linear recurrences

A linear recurrence propagates any other linear recurrence that holds on a
sufficiently long initial window.
-/

namespace MetaMathlibExt

/-- **Finite window criterion for linear recurrences.** Let $R$ be a commutative ring, let
$x, A, a : \mathbb{N} \to R$ and let $r, s, N \in \mathbb{N}$. Suppose that
$x_n = \sum_{i=1}^{r} A_i x_{n-i}$ for all $n \ge r$, that $N \ge r + s - 1$, and that
$x_n = \sum_{i=1}^{s} a_i x_{n-i}$ for all $n$ with $s \le n \le N$. Then
$x_n = \sum_{i=1}^{s} a_i x_{n-i}$ for all $n \ge s$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 1. -/
public theorem linearRecurrence_of_finite_window {R : Type*} [CommRing R]
    (x A a : ℕ → R) (r s N : ℕ)
    (hA : ∀ n, r ≤ n → x n = ∑ i ∈ Finset.Icc 1 r, A i * x (n - i))
    (hN : r + s - 1 ≤ N)
    (ha : ∀ n, s ≤ n → n ≤ N → x n = ∑ i ∈ Finset.Icc 1 s, a i * x (n - i)) :
    ∀ n, s ≤ n → x n = ∑ i ∈ Finset.Icc 1 s, a i * x (n - i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hsn
    by_cases hn : n ≤ N
    · exact ha n hsn hn
    have hrs : r + s ≤ n := by omega
    calc
      x n = ∑ i ∈ Finset.Icc 1 r, A i * x (n - i) := hA n (by omega)
      _ = ∑ i ∈ Finset.Icc 1 r, ∑ j ∈ Finset.Icc 1 s,
          A i * (a j * x (n - i - j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨hi₁, hir⟩ := Finset.mem_Icc.mp hi
        rw [ih (n - i) (by omega) (by omega), Finset.mul_sum]
      _ = ∑ j ∈ Finset.Icc 1 s, ∑ i ∈ Finset.Icc 1 r,
          a j * (A i * x (n - j - i)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Nat.sub_right_comm, mul_left_comm]
      _ = ∑ j ∈ Finset.Icc 1 s, a j * x (n - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjs := (Finset.mem_Icc.mp hj).2
        rw [← Finset.mul_sum, ← hA (n - j) (by omega)]

end MetaMathlibExt
