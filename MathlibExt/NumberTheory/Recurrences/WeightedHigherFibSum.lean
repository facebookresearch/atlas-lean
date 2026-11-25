/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Weighted sums of higher-order Fibonacci sequences

`weightedHigherFibSum_eq` expresses a finite geometric weighting of an integer-indexed
$m$-step Fibonacci sequence in terms of values near the endpoints.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

/-- **The $m$-step Fibonacci recurrence.** A sequence $F : \mathbb{Z} \to \mathbb{Q}$ satisfies the
$m$-step Fibonacci recurrence if $F_n = F_{n-1} + F_{n-2} + \dots + F_{n-m}$ for every integer
$n$, that is, $F_n = \sum_{i=0}^{m-1} F_{n-i-1}$. For $m = 0$ this says $F_n = 0$ for all $n$. -/
def IsHigherFibRecurrence (m : ℕ) (F : ℤ → ℚ) : Prop :=
  ∀ n : ℤ, F n = ∑ i ∈ Finset.range m, F (n - (i : ℤ) - 1)

/-- **Weighted sum of a sequence.** For a sequence $F : \mathbb{Z} \to \mathbb{Q}$, a natural number
$m$, integers $N$ and $l$, and a rational number $q$, $S(m,N,l,q) = \sum_{k=0}^{N} q^k F_{k+l}$;
for $N < 0$ this is the empty sum $0$.

The order $m$ is carried explicitly to match the paper notation, although the sum itself only
uses $F$, $N$, $l$, and $q$. -/
def weightedHigherFibSum (F : ℤ → ℚ) (_m : ℕ) (N l : ℤ) (q : ℚ) : ℚ :=
  if N < 0 then
    0
  else
    ∑ k ∈ Finset.range (N.toNat + 1), q ^ (k : ℤ) * F ((k : ℤ) + l)

/-- Shifting the summation window by one leaves only its two endpoints. -/
private lemma weightedSum_shift (F : ℤ → ℚ) (m n : ℕ) (l : ℤ) (q : ℚ) :
    q ^ (n + 1) * F ((n : ℤ) + l + 1) - F l =
      q * weightedHigherFibSum F m n (l + 1) q - weightedHigherFibSum F m n l q := by
  let f (k : ℕ) := q ^ k * F ((k : ℤ) + l)
  calc
    _ = f (n + 1) - f 0 := by simp [f, add_right_comm]
    _ = ∑ k ∈ Finset.range (n + 1), (f (k + 1) - f k) := (Finset.sum_range_sub f _).symm
    _ = _ := by
      simp only [weightedHigherFibSum, Int.natCast_nonneg, not_lt.mpr, ite_false, Int.toNat_natCast,
        zpow_natCast, Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      simp [f, pow_succ', add_assoc, add_comm (1 : ℤ) l, mul_assoc]

/-- In each row of the double sum the differences telescope across the shifts. -/
private lemma sum_shift_differences (S : ℤ → ℚ) (q : ℚ) (l : ℤ) (i : ℕ) :
    ∑ j ∈ Finset.Icc 1 i, q ^ (i + 1 - j) * (q * S (l - j + 1) - S (l - j)) =
      q ^ (i + 1) * S l - q * S (l - i) := by
  let f (j : ℕ) := q ^ (i + 1 - j) * S (l - j)
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  calc
    _ = ∑ j ∈ Finset.range i, (f j - f (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have he : i + 1 - j = (i + 1 - (1 + j)) + 1 := by omega
      simp only [f, Nat.cast_add, Nat.cast_one]
      rw [he, pow_succ, add_comm j 1, show l - (1 + (j : ℤ)) + 1 = l - j by ring,
        add_comm (j : ℤ) 1]
      ring
    _ = f 0 - f i := Finset.sum_range_sub' f i
    _ = _ := by simp [f]

/-- **Closed form for weighted sums of an $m$-step Fibonacci sequence.** Let $m \ge 1$ and let
$F : \mathbb{Z} \to \mathbb{Q}$ satisfy the $m$-step Fibonacci recurrence
$F_k = F_{k-1} + \dots + F_{k-m}$ for every integer $k$. For every natural number $n$, every
integer $l$ and every rational number $q$ with $q^{m+1} - 2q + 1 \ne 0$, the weighted sum
$S(m,n,l,q) = \sum_{k=0}^{n} q^k F_{k+l}$ equals
$$
\frac{(q-1)\Bigl(q^{n+1}F_{n+l+1} - F_l +
\sum_{i=1}^{m-1}\sum_{j=1}^{i} q^{i+1-j}\bigl(q^{n+1}F_{n+l-j+1} - F_{l-j}\bigr)\Bigr)}
{q^{m+1} - 2q + 1}.
$$

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 2. -/
theorem weightedHigherFibSum_eq
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsHigherFibRecurrence m F)
    (n : ℕ) (l : ℤ) (q : ℚ)
    (hq : q ^ (m + 1) - 2 * q + 1 ≠ 0) :
    weightedHigherFibSum F m (n : ℤ) l q =
      ((q - 1) *
        (q ^ (n + 1) * F ((n : ℤ) + l + 1) - F l +
          ∑ i ∈ Finset.Icc 1 (m - 1),
            ∑ j ∈ Finset.Icc 1 i,
              q ^ (i + 1 - j) *
                (q ^ (n + 1) * F ((n : ℤ) + l - (j : ℤ) + 1) -
                  F (l - (j : ℤ))))) /
        (q ^ (m + 1) - 2 * q + 1) := by
  let S (t : ℤ) := weightedHigherFibSum F m n t q
  have hrec : S (l + 1) = ∑ i ∈ Finset.range m, S (l - i) := by
    simp only [S, weightedHigherFibSum, Int.natCast_nonneg, not_lt.mpr, ite_false,
      Int.toNat_natCast]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [hF ((k : ℤ) + (l + 1)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (k : ℤ) + (l + 1) - i - 1 = k + (l - i) by ring]
  have hrow (i : ℕ) :
      ∑ j ∈ Finset.Icc 1 i, q ^ (i + 1 - j) *
        (q ^ (n + 1) * F ((n : ℤ) + l - j + 1) - F (l - j)) =
        q ^ (i + 1) * S l - q * S (l - i) := by
    rw [← sum_shift_differences S q l i]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (n : ℤ) + l - j + 1 = n + (l - j) + 1 by ring, weightedSum_shift]
  -- The missing row at zero vanishes, so the recurrence cancels all shifted sums.
  let row (i : ℕ) := q ^ (i + 1) * S l - q * S (l - i)
  have hrows : ∑ i ∈ Finset.Icc 1 (m - 1), row i = ∑ i ∈ Finset.range m, row i := by
    rw [Finset.sum_range_eq_add_Ico row hm, ← Finset.Ico_add_one_right_eq_Icc,
      Nat.sub_add_cancel hm]
    simp [row]
  apply (eq_div_iff hq).2
  simp_rw [hrow]
  change S l * _ = (q - 1) * (_ + ∑ i ∈ Finset.Icc 1 (m - 1), row i)
  rw [weightedSum_shift, hrows]
  change S l * _ = (q - 1) * (q * S (l + 1) - S l + _)
  simp only [row, pow_succ q, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← hrec]
  linear_combination -q * S l * geom_sum_mul q m

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
