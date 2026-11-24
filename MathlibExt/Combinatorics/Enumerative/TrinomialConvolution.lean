/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TrinomialCoefficient
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.ComputeDegree

/-!
# Vandermonde convolution for trinomial coefficients

Reversing the coefficients of the second row turns the shifted sum into a coefficient
of the product of the two row polynomials.
-/

open Polynomial

namespace MetaMathlibExt

local notation "P" => (1 + X + X ^ 2 : ℕ[X])

private theorem natDegree_trinomial_pow_le (m : ℕ) : (P ^ m).natDegree ≤ 2 * m := by
  rw [Nat.mul_comm]
  compute_degree

private theorem reflect_trinomial_pow (m : ℕ) : reflect (2 * m) (P ^ m) = P ^ m := by
  have hdeg : natDegree P ≤ 2 := by compute_degree
  have hbase : reflect 2 P = P := by
    have hX : reflect 2 (X : ℕ[X]) = X := by
      simpa [revAt_le (by decide : 1 ≤ 2)] using reflect_monomial (R := ℕ) 2 1
    simp [hX, revAt_le, add_comm, add_assoc]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, pow_succ, reflect_mul _ _ (natDegree_trinomial_pow_le m) hdeg, ih, hbase]

/-- **Vandermonde convolution for trinomial coefficients.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $t^k$ in $(1 + t + t^2)^n$, and put $\binom{n}{k}_2 = 0$
for negative integers $k$. Then for all natural numbers $n$, $m$ and every integer $l$,

$$\sum_{k=0}^{2m} \binom{n}{l + k}_2 \binom{m}{k}_2 = \binom{n + m}{2m + l}_2.$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 20 (`jis-2025-25.3.5-thm-20`). -/
public theorem sum_trinomialCoefficient_convolution (n m : ℕ) (l : ℤ) :
    ∑ k ∈ Finset.range (2 * m + 1),
        (if 0 ≤ l + k then trinomialCoefficient n (l + k).toNat else 0) *
          trinomialCoefficient m k =
      if 0 ≤ 2 * m + l then trinomialCoefficient (n + m) (2 * m + l).toNat else 0 := by
  by_cases hl : 0 ≤ 2 * (m : ℤ) + l
  · -- Reverse the summation so that the second row supplies the exponent of each monomial.
    rw [ite_eq_left hl, ← Finset.sum_range_reflect]
    simp only [Nat.add_sub_cancel]
    unfold trinomialCoefficient
    have hdeg := Nat.lt_succ_of_le (natDegree_trinomial_pow_le m)
    conv_rhs =>
      rw [pow_add, (P ^ m).as_sum_range_C_mul_X_pow' hdeg,
        Finset.mul_sum, finsetSum_coeff]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ 2 * m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hsymm := congrArg (fun p : ℕ[X] => p.coeff k) (reflect_trinomial_pow m)
    simp only [coeff_reflect, revAt_le hk'] at hsymm
    rw [hsymm, ← mul_assoc, coeff_mul_X_pow']
    by_cases h : k ≤ (2 * (m : ℤ) + l).toNat
    · rw [ite_eq_left h, coeff_mul_C, ite_eq_left (by omega)]
      congr 2
      omega
    · rw [ite_eq_right h, ite_eq_right (by omega), zero_mul]
  · rw [ite_eq_right hl]
    refine Finset.sum_eq_zero fun k hk => ?_
    have := Finset.mem_range.mp hk
    rw [ite_eq_right (by omega), zero_mul]

end MetaMathlibExt
