/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating functions of decimated linear recurrences

Multiplying the generating series by the recurrence denominator cancels all terms of
degree at least `m * r`. At smaller degrees the coefficient is the decimation coefficient
with quotient and remainder indices for division by the stride `r`.
-/

namespace MetaMathlibExt

open Finset PowerSeries

@[expose] public section

/-- **Decimation coefficients.** Let $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ be sequences in a
commutative ring and let $m$, $r$ be natural numbers. For natural numbers $l$ and $i$, the
decimation coefficient is
$$v_l^{(i)} = s_{lr+i} - \sum_{j<l} A_{m-1-j} s_{(l-1-j)r+i},$$
an index $m-1-j$ that would be negative being read as $0$. For $l \le m$ this is
$v_l^{(i)} = s_{lr+i} - A_{m-1} s_{(l-1)r+i} - \cdots - A_{m-l} s_i$.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1. -/
public def decimationCoeff {R : Type*} [CommRing R] (A s : ℕ → R) (m r l i : ℕ) : R :=
  s (l * r + i) - ∑ j ∈ Finset.range l, A (m - 1 - j) * s ((l - 1 - j) * r + i)

/-- **Zeroth decimation coefficient.** For sequences $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ in
a commutative ring and natural numbers $m$, $r$, $i$, the decimation coefficient $v_0^{(i)}$
equals $s_i$.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1. -/
public theorem decimationCoeff_zero {R : Type*} [CommRing R] (A s : ℕ → R) (m r i : ℕ) :
    decimationCoeff A s m r 0 i = s i := by
  simp [decimationCoeff]

/-- **First decimation coefficient.** For sequences $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ in a
commutative ring and natural numbers $m$, $r$, $i$, the decimation coefficient $v_1^{(i)}$
equals $s_{r+i} - A_{m-1} s_i$, where $A_{m-1}$ is read as $A_0$ when $m = 0$.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1. -/
public theorem decimationCoeff_one {R : Type*} [CommRing R] (A s : ℕ → R) (m r i : ℕ) :
    decimationCoeff A s m r 1 i = s (r + i) - A (m - 1) * s i := by
  simp [decimationCoeff]

namespace decimation_generating_function

/-- The degree selects the residue class and the index in that class. -/
private theorem coeff_numerator {R : Type*} [CommRing R] (v : ℕ → ℕ → R) (m r n : ℕ) :
    coeff n (∑ i ∈ range r, ∑ l ∈ range m, C (v l i) * X ^ (l * r + i)) =
      if n < m * r then v (n / r) (n % r) else 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  simp only [map_sum, coeff_C_mul_X_pow]
  have inner (i : ℕ) (hi : i ∈ range r) :
      (∑ l ∈ range m, if n = l * r + i then v l i else 0) =
        if n % r = i then (if n / r < m then v (n / r) i else 0) else 0 := by
    have index (l : ℕ) : n = l * r + i ↔ n % r = i ∧ n / r = l := by
      rw [and_comm, Nat.div_mod_unique hr]
      simp [mem_range.mp hi, Nat.add_comm, Nat.mul_comm, eq_comm]
    by_cases h : n % r = i <;> simp [index, h]
  rw [sum_congr rfl inner, sum_ite_eq]
  simp [Nat.mod_lt n hr, Nat.div_lt_iff_lt_mul hr]

/-- Below degree `m * r`, only shifts up to `n / r` contribute to the coefficient. -/
private theorem initial_shifts {R : Type*} [CommRing R] (A s : ℕ → R) {m r n : ℕ}
    (hr : 0 < r) (hn : n / r < m) :
    (∑ j ∈ range m, if (m - j) * r ≤ n then A j * s (n - (m - j) * r) else 0) =
      ∑ j ∈ range (n / r), A (m - 1 - j) * s ((n / r - 1 - j) * r + n % r) := by
  rw [← sum_range_reflect _ m]
  refine (sum_subset (range_mono hn.le) ?_).symm.trans ?_
  · intro j hj hout
    simp only [mem_range] at hj hout
    have hshift : m - (m - 1 - j) = j + 1 := by omega
    rw [hshift, ite_eq_right]
    rwa [← Nat.le_div_iff_mul_le hr]
  · apply sum_congr rfl
    intro j hj
    simp only [mem_range] at hj
    have hshift : m - (m - 1 - j) = j + 1 := by omega
    rw [hshift, ite_eq_left ((Nat.le_div_iff_mul_le hr).mp hj)]
    have hsplit := Nat.div_add_mod' n r
    have hle : (j + 1) * r ≤ n / r * r := Nat.mul_le_mul_right r hj
    rw [show n / r - 1 - j = n / r - (j + 1) by omega, Nat.sub_mul]
    congr 2
    omega

end decimation_generating_function

/-- **Generating function of a decimated linear recurrence.** Let $R$ be a commutative ring,
let $m$ and $r$ be natural numbers, and let $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ be
sequences in $R$ such that $s_{n+mr} = \sum_{j<m} A_j s_{n+jr}$ for all $n \ge 0$. Then, in
the ring $R[[x]]$ of formal power series,
$$
\Bigl(\sum_{n \ge 0} s_n x^n\Bigr)\Bigl(1 - \sum_{j<m} A_j x^{(m-j)r}\Bigr) =
\sum_{i<r} \sum_{l<m} v_l^{(i)} x^{lr+i},
$$
where $v_l^{(i)} = s_{lr+i} - \sum_{j<l} A_{m-1-j} s_{(l-1-j)r+i}$ are the decimation
coefficients. The second factor on the left is the denominator
$1 - A_{m-1} x^r - A_{m-2} x^{2r} - \cdots - A_0 x^{mr}$ of the generating function.

The printed denominator ends in $- A_1 x^{mr} - A_0$ and the printed hypothesis names
Relation (1); this is the reading of the paper's derivation and of its Example 2 ($m = 2$:
$1 - A_1 x^r - A_0 x^{2r}$).

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1 (`integers-2026-A5-thm-1`). -/
public theorem decimation_generating_function {R : Type*} [CommRing R] {m r : ℕ}
    {A s : ℕ → R} (hs : ∀ n, s (n + m * r) = ∑ j ∈ Finset.range m, A j * s (n + j * r)) :
    PowerSeries.mk s *
        (1 - ∑ j ∈ Finset.range m, PowerSeries.C (A j) * PowerSeries.X ^ ((m - j) * r)) =
      ∑ i ∈ Finset.range r, ∑ l ∈ Finset.range m,
        PowerSeries.C (decimationCoeff A s m r l i) * PowerSeries.X ^ (l * r + i) := by
  apply PowerSeries.ext
  intro n
  rw [decimation_generating_function.coeff_numerator]
  simp only [mul_sub, mul_one, Finset.mul_sum, ← mul_assoc, map_sub, map_sum,
    coeff_mul_X_pow', coeff_mul_C, coeff_mk, mul_comm _ (A _)]
  by_cases hn : n < m * r
  · have hr := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt hn)
    rw [ite_eq_left hn, decimation_generating_function.initial_shifts A s hr
      ((Nat.div_lt_iff_lt_mul hr).mpr hn)]
    simp only [decimationCoeff, Nat.div_add_mod']
  · rw [ite_eq_right hn, sub_eq_zero]
    have hm : m * r ≤ n := Nat.le_of_not_gt hn
    have hrec := hs (n - m * r)
    rw [Nat.sub_add_cancel hm] at hrec
    refine hrec.trans (sum_congr rfl fun j hj ↦ ?_)
    have hjm := Nat.mul_le_mul_right r (mem_range.mp hj).le
    rw [Nat.sub_mul, ite_eq_left (by omega), show n - (m * r - j * r) = n - m * r + j * r by omega]

end

end MetaMathlibExt
