/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import MathlibExt.NumberTheory.TrinomialCoefficient
import MathlibExt.Combinatorics.Enumerative.TrinomialConvolution
import Mathlib.Tactic.LinearCombination

/-!
# The upper half of a trinomial row

Multiplication by `1 + X + X ^ 2` gives a recurrence for the weighted half-row.
The two neighbors of the central coefficient agree by reflection of the row.
-/

namespace MetaMathlibExt

open Polynomial

local notation "P" => (1 + X + X ^ 2 : ℕ[X])

-- Convolution with row zero reflects the column index in the other row.
private theorem adjacent_reflection (n : ℕ) :
    trinomialCoefficient (n + 1) n = trinomialCoefficient (n + 1) (n + 2) := by
  have h := sum_trinomialCoefficient_convolution 0 (n + 1) (-(n : ℤ))
  have hterm (k : ℕ) :
      (if 0 ≤ -(n : ℤ) + k then trinomialCoefficient 0 (-(n : ℤ) + k).toNat else 0) =
        if n = k then 1 else 0 := by
    simp only [trinomialCoefficient, pow_zero, coeff_one]
    split_ifs <;> omega
  have hcol : 2 * (↑(n + 1) : ℤ) + -↑n = ↑(n + 2) := by omega
  simp only [hterm, hcol, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Int.natCast_nonneg,
    ite_true, Int.toNat_natCast] at h
  simpa [show n < 2 * (n + 1) + 1 by omega] using h

private theorem central_succ (n : ℕ) :
    trinomialCoefficient (n + 1) (n + 1) =
      trinomialCoefficient n n + 2 * trinomialCoefficient n (n + 1) := by
  cases n with
  | zero => simp [trinomialCoefficient, coeff_one, coeff_add, coeff_X, coeff_X_pow]
  | succ n =>
    have h := adjacent_reflection n
    unfold trinomialCoefficient at h ⊢
    rw [pow_succ P (n + 1), mul_add, mul_add, mul_one, coeff_add, coeff_add,
      coeff_mul_X, coeff_mul_X_pow, h, two_mul]
    ac_rfl

/-- Evaluate the coefficients through degree `n` in descending order, starting at weight one. -/
private noncomputable def weightedPrefix (p : ℕ[X]) (w : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (p.coeff (n - k) : ℂ) * w ^ k

private theorem weightedPrefix_succ (p : ℕ[X]) (w : ℂ) (n : ℕ) :
    weightedPrefix p w (n + 1) = weightedPrefix p w n * w + p.coeff (n + 1) := by
  unfold weightedPrefix
  rw [Finset.sum_range_succ', Finset.sum_mul]
  simp [pow_succ, mul_assoc]

private theorem weightedPrefix_mul_X (p : ℕ[X]) (w : ℂ) (n : ℕ) :
    weightedPrefix (p * X) w (n + 1) = weightedPrefix p w n := by
  induction n with
  | zero => simp [weightedPrefix, Finset.sum_range_succ]
  | succ n ih => rw [weightedPrefix_succ, ih, coeff_mul_X, ← weightedPrefix_succ]

private theorem weightedPrefix_add (p q : ℕ[X]) (w : ℂ) (n : ℕ) :
    weightedPrefix (p + q) w n = weightedPrefix p w n + weightedPrefix q w n := by
  simp [weightedPrefix, coeff_add, add_mul, Finset.sum_add_distrib]

private theorem weightedPrefix_row_succ (n : ℕ) (w : ℂ) :
    weightedPrefix (P ^ (n + 1)) w (n + 1) * w =
      (1 + w + w ^ 2) * weightedPrefix (P ^ n) w n +
        (trinomialCoefficient n (n + 1) : ℂ) * w - trinomialCoefficient n n := by
  have h := weightedPrefix_succ (P ^ n * X) w n
  rw [weightedPrefix_mul_X, coeff_mul_X] at h
  have hshift (p : ℕ[X]) : p * X ^ 2 = p * X * X := by rw [mul_assoc, sq]
  rw [pow_succ, mul_add, mul_add, mul_one, hshift,
    weightedPrefix_add, weightedPrefix_add, weightedPrefix_mul_X, weightedPrefix_mul_X,
    weightedPrefix_succ]
  unfold trinomialCoefficient
  linear_combination -h

/-- **Generating sum of the upper half of a trinomial row.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For every natural number $n$
and every complex number $w$,
$$\sum_{k=0}^{n} \binom{n}{n-k}_2 w^{n+k} = \frac{(1+w+w^2)^n}{2} + \frac{\binom{n}{n}_2 w^n}{2} +
\frac{w^2-1}{2} \sum_{k=0}^{n-1} \binom{k}{k}_2 (1+w+w^2)^{n-1-k} w^k.$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 40 (`jis-2025-25.3.5-cor-40`). -/
public theorem sum_trinomialCoefficient_upper_half (n : ℕ) (w : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (n - k) : ℂ) * w ^ (n + k) =
      (1 + w + w ^ 2) ^ n / 2 + (trinomialCoefficient n n : ℂ) * w ^ n / 2 +
        (w ^ 2 - 1) / 2 * ∑ k ∈ Finset.range n,
          (trinomialCoefficient k k : ℂ) * (1 + w + w ^ 2) ^ (n - 1 - k) * w ^ k := by
  let a := 1 + w + w ^ 2
  let s (m : ℕ) := ∑ k ∈ Finset.range m,
    (trinomialCoefficient k k : ℂ) * a ^ (m - 1 - k) * w ^ k
  suffices weightedPrefix (P ^ n) w n * w ^ n =
      a ^ n / 2 + (trinomialCoefficient n n : ℂ) * w ^ n / 2 + (w ^ 2 - 1) / 2 * s n by
    rw [← this, weightedPrefix, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [pow_add]; unfold trinomialCoefficient; ring
  induction n with
  | zero => norm_num [weightedPrefix, trinomialCoefficient_zero_zero, s]
  | succ n ih =>
    have hs : s (n + 1) = a * s n + (trinomialCoefficient n n : ℂ) * w ^ n := by
      unfold s
      rw [Finset.sum_range_succ, Finset.mul_sum]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [show n - k = n - 1 - k + 1 by omega, pow_succ]
      ring
    have hc : (trinomialCoefficient (n + 1) (n + 1) : ℂ) =
        trinomialCoefficient n n + 2 * (trinomialCoefficient n (n + 1) : ℂ) := by
      exact_mod_cast central_succ n
    calc
      _ = (weightedPrefix (P ^ (n + 1)) w (n + 1) * w) * w ^ n := by rw [pow_succ w]; ring
      _ = _ := by
        rw [weightedPrefix_row_succ, hc, hs, pow_succ a, pow_succ w]
        simp only [a] at ih ⊢
        linear_combination (1 + w + w ^ 2) * ih

end MetaMathlibExt
