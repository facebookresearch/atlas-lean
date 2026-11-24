/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Step sums and finite recurrence windows

The Riordan-array step sums are coefficients of a geometric series. A linear recurrence
propagates any other linear recurrence that holds on a sufficiently long initial window.
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

/-- **Step sums along a Riordan array.** Let $K$ be a field, let $g, h \in K[[x]]$ with
$h(0) = 0$, and write $d(n, m) = [x^n]\, g(x) h(x)^m$. Then for all natural numbers $k > 1$,
$p < k$ and $n$,
$\sum_{j=0}^{n} d(n, kj + p) = [x^n]\, g(x) h(x)^p (1 - h(x)^k)^{-1}$.

Since $h(0) = 0$, $d(n, m) = 0$ for $m > n$, so the left side is the full sum over all
$j \ge 0$.

Source: Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and
Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 5. -/
public theorem riordan_stepSum_coeff {K : Type*} [Field K] (g h : PowerSeries K)
    (hh : PowerSeries.constantCoeff h = 0) (k p : ℕ) (hk : 1 < k) (hp : p < k) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff n (g * h ^ (k * j + p)) =
      PowerSeries.coeff n (g * h ^ p * (1 - h ^ k)⁻¹) := by
  let q := h ^ k
  let u := g * h ^ p * (1 - q)⁻¹
  have hk₀ : k ≠ 0 := (lt_of_le_of_lt (Nat.zero_le p) hp).ne'
  have hq : PowerSeries.constantCoeff q = 0 := by
    simp only [q, map_pow, hh, zero_pow hk₀]
  have hunit : PowerSeries.constantCoeff (1 - q) ≠ 0 := by simp [hq]
  have hu : u * (1 - q) = g * h ^ p := by
    rw [show u = g * h ^ p * (1 - q)⁻¹ from rfl, mul_assoc,
      PowerSeries.inv_mul_cancel _ hunit, mul_one]
  have hdegree : n < k * (n + 1) := by
    refine (Nat.lt_succ_self n).trans_le ?_
    simpa only [one_mul] using Nat.mul_le_mul_right (n + 1) hk.le
  have horder : (n : ℕ∞) < (q ^ (n + 1)).order := by
    change (n : ℕ∞) < ((h ^ k) ^ (n + 1)).order
    rw [← pow_mul]
    have hcast : (n : ℕ∞) < ((k * (n + 1) : ℕ) : ℕ∞) := by exact_mod_cast hdegree
    exact hcast.trans_le (PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ hh)
  calc
    _ = PowerSeries.coeff n (g * h ^ p * ∑ j ∈ Finset.range (n + 1), q ^ j) := by
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [q, pow_mul, pow_add]
      congr 1
      ac_rfl
    _ = PowerSeries.coeff n (u * (1 - q ^ (n + 1))) := by
      rw [← geom_sum_mul_neg q (n + 1), ← hu]
      congr 1
      ac_rfl
    _ = _ := PowerSeries.coeff_mul_one_sub_of_lt_order n horder

end MetaMathlibExt
