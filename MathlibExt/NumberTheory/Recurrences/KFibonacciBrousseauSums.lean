/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
public import MathlibExt.NumberTheory.LucasSequence

/-! # Power-weighted convolutions of the k-Fibonacci numbers -/

namespace MetaMathlibExt

@[expose] public section

/-- **The numbers $A_k^{(p)}$ for $k$-Fibonacci Brousseau sums.** For a rational number $k$, the
rational numbers $A_k^{(p)}$, $p \ge 0$, are defined by $A_k^{(0)} = 1$ and, for $p \ge 1$,
$$
A_k^{(p)} = \frac{2}{k} \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} A_k^{(p-2j+1)},
$$
where $2/k$ is read as $0$ when $k = 0$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
def brousseauA (k : ℚ) : ℕ → ℚ
  | 0 => 1
  | p + 1 => 2 / k * ∑ j ∈ Finset.range ((p + 2) / 2),
      ((p + 1).choose (2 * j + 1) : ℚ) * brousseauA k (p - 2 * j)
decreasing_by omega

/-- **The initial value $A_k^{(0)} = 1$.** For every rational number $k$, the number $A_k^{(0)}$
for $k$-Fibonacci Brousseau sums equals $1$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
theorem brousseauA_zero (k : ℚ) : brousseauA k 0 = 1 := by
  rw [brousseauA]

/-- **The value $A_k^{(1)} = 2/k$.** For every rational number $k$, the number $A_k^{(1)}$ for
$k$-Fibonacci Brousseau sums equals $2/k$, where $2/0$ is read as $0$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
theorem brousseauA_one (k : ℚ) : brousseauA k 1 = 2 / k := by
  rw [brousseauA]
  simp [brousseauA_zero]

/-- **The value $A_k^{(2)} = 8/k^2$.** For every rational number $k$, the number $A_k^{(2)}$ for
$k$-Fibonacci Brousseau sums equals $8/k^2$, where $8/0$ is read as $0$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
theorem brousseauA_two (k : ℚ) : brousseauA k 2 = 8 / k ^ 2 := by
  rw [brousseauA]
  simp [brousseauA_one]
  ring

/-- **The coefficient polynomials $C_k^{(p)}$ for $k$-Fibonacci Brousseau sums.** For a rational
number $k$, let $A_k^{(r)}$ be the numbers for $k$-Fibonacci Brousseau sums. For a natural number
$p$ and a rational number $n$,
$$
C_k^{(p)}(n) = \sum_{r=0}^{p} (-1)^r A_k^{(r)} \binom{p}{r} n^{p-r},
$$
where $0^0 = 1$; in particular $C_k^{(p)}(0) = (-1)^p A_k^{(p)}$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 5. -/
def brousseauCoeff (k : ℚ) (p : ℕ) (n : ℚ) : ℚ :=
  ∑ r ∈ Finset.range (p + 1), (-1) ^ r * brousseauA k r * (p.choose r : ℚ) * n ^ (p - r)

/-- **The polynomial $C_k^{(0)}$ is constant $1$.** For all rational numbers $k$ and $n$, the
coefficient polynomial $C_k^{(0)}$ for $k$-Fibonacci Brousseau sums satisfies $C_k^{(0)}(n) = 1$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 5. -/
theorem brousseauCoeff_zero (k n : ℚ) : brousseauCoeff k 0 n = 1 := by
  simp [brousseauCoeff, brousseauA_zero]

/-- **The polynomial $C_k^{(1)}(n) = n - 2/k$.** For all rational numbers $k$ and $n$, the
coefficient polynomial $C_k^{(1)}$ for $k$-Fibonacci Brousseau sums satisfies
$C_k^{(1)}(n) = n - 2/k$, where $2/0$ is read as $0$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 5. -/
theorem brousseauCoeff_one (k n : ℚ) : brousseauCoeff k 1 n = n - 2 / k := by
  simp [brousseauCoeff, Finset.sum_range_succ, brousseauA_zero, brousseauA_one]
  ring

open Finset

namespace kFibonacci_eq_pow_add_convolution

private lemma pow_difference (x : ℤ) (p : ℕ) :
    (x + 1) ^ p - (x - 1) ^ p =
      2 * ∑ j ∈ Icc 1 ((p + 1) / 2),
        (p.choose (2 * j - 1) : ℤ) * x ^ (p + 1 - 2 * j) := by
  let term (r : ℕ) := (p.choose r : ℤ) * x ^ (p - r)
  calc
    _ = ∑ r ∈ range (p + 1), (1 - (-1 : ℤ) ^ r) * term r := by
      rw [add_comm x 1, sub_eq_add_neg x 1, add_comm x (-1), add_pow, add_pow, ← sum_sub_distrib]
      refine sum_congr rfl fun r _ ↦ ?_
      simp only [one_pow, one_mul, term]
      ring
    _ = 2 * ∑ r ∈ (range (p + 1)).filter (fun r ↦ r % 2 = 1), term r := by
      rw [mul_sum, sum_filter]
      refine sum_congr rfl fun r _ ↦ ?_
      rw [neg_one_pow_eq_pow_mod_two]
      rcases Nat.mod_two_eq_zero_or_one r with h | h <;> simp [h, two_mul]
    _ = _ := by
      congr 1
      symm
      apply sum_bij (fun j _ ↦ 2 * j - 1)
      · simp only [mem_Icc, mem_filter, mem_range]
        omega
      · simp only [mem_Icc]
        omega
      · intro r hr
        simp only [mem_filter, mem_range] at hr
        refine ⟨(r + 1) / 2, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro j hj
        have hj_pos := (mem_Icc.mp hj).1
        simp only [term, show p - (2 * j - 1) = p + 1 - 2 * j by omega]

end kFibonacci_eq_pow_add_convolution

-- Keep the nonzero proofs in the Lucas parameters inline, as in the wanted statement.
set_option backward.proofsInPublic true in
/-- **$k$-Fibonacci numbers as a power-weighted convolution.** For an integer $k$, let $F_{k,n}$
be the $k$-Fibonacci numbers, the Lucas sequence $U(k, -1)$: $F_{k,0} = 0$, $F_{k,1} = 1$ and
$F_{k,n+2} = k F_{k,n+1} + F_{k,n}$. For every integer $k$, every $n \ge 0$ and every $p \ge 1$,
$$
F_{k,n} = n^p + \sum_{i=1}^{n} \Bigl(k i^p -
2 \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} i^{p-2j+1}\Bigr) F_{k,n-i}.
$$

The paper assumes $k \ge 1$ and $n \ge 1$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 1 (`jis-2024-24.6.4-thm-1`). -/
theorem kFibonacci_eq_pow_add_convolution (k : ℤ) (n p : ℕ) (hp : 1 ≤ p) :
    lucasU ⟨k, -1, by decide⟩ n = (n : ℤ) ^ p +
      ∑ i ∈ Finset.Icc 1 n, (k * (i : ℤ) ^ p -
        2 * ∑ j ∈ Finset.Icc 1 ((p + 1) / 2),
          (p.choose (2 * j - 1) : ℤ) * (i : ℤ) ^ (p + 1 - 2 * j)) *
        lucasU ⟨k, -1, by decide⟩ (n - i) := by
  let U := lucasU ⟨k, -1, by decide⟩
  let weight (i : ℕ) := k * (i : ℤ) ^ p - (((i : ℤ) + 1) ^ p - ((i : ℤ) - 1) ^ p)
  simp_rw [← kFibonacci_eq_pow_add_convolution.pow_difference]
  change U n = (n : ℤ) ^ p + ∑ i ∈ Icc 1 n, weight i * U (n - i)
  cases n with
  | zero => simp [U, lucasU, zero_pow (by omega : p ≠ 0)]
  | succ n =>
    -- Consecutive values of T differ by one term of the convolution.
    let T (i : ℕ) := ((i : ℤ) + 1) ^ p * U (n + 1 - i) + (i : ℤ) ^ p * U (n - i)
    have step (i : ℕ) (hi : i < n) :
        weight (i + 1) * U (n - i) = T i - T (i + 1) := by
      have recurrence : U (n + 1 - i) = k * U (n - i) + U (n - (i + 1)) := by
        simpa only [U, neg_one_mul, sub_neg_eq_add,
          show n - (i + 1) + 2 = n + 1 - i by omega,
          show n - (i + 1) + 1 = n - i by omega] using
          lucasU_add_two ⟨k, -1, by decide⟩ (n - (i + 1))
      simp only [T, weight, Nat.cast_add_one, Nat.add_sub_add_right, add_sub_cancel_right]
      rw [recurrence]
      ring
    rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1), ← Ico_add_one_right_eq_Icc 1 n,
      sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm 1, Nat.add_sub_add_right, Nat.sub_self,
      show U 0 = 0 from rfl, mul_zero, add_zero]
    rw [sum_congr rfl (fun i hi ↦ step i (mem_range.mp hi)), sum_range_sub']
    simp [T, U, lucasU, zero_pow (by omega : p ≠ 0)]

end

end MetaMathlibExt
