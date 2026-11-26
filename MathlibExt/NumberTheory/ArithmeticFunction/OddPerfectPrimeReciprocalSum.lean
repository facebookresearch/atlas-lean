/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EulerPrime
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-! # Fifth-power bound on the Euler prime of an odd perfect number

The main result is `eulerianForm_exponent_eq_one_or_pow_five_lt`: if `(n, q, e, m)` is in
Eulerian form then `e = 1` or `q ^ 5 < 2 * m ^ 2`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 11.
-/

namespace MetaMathlibExt

/-- **Fifth-power bound on the Euler prime of an odd perfect number.** If $(n, q, e, m)$ is in
Eulerian form, that is, $n$ is an odd perfect number, $q$ is a prime coprime to $m$,
$n = q^e m^2$ and $q \equiv e \equiv 1 \pmod 4$, then $e = 1$ or $q^5 < 2m^2$, that is,
$q < 2^{1/5} m^{2/5}$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 11 (`integers-2025-A59-prop-11`). -/
public theorem eulerianForm_exponent_eq_one_or_pow_five_lt
    (n q e m : ℕ) (h : EulerianForm n q e m) :
    e = 1 ∨ q ^ 5 < 2 * m ^ 2 := by
  obtain ⟨hperf, _hodd, hq, hnm, _hq4, he4, hcop⟩ := h
  by_cases he1 : e = 1
  · exact Or.inl he1
  · right
    have he5 : 5 ≤ e := by omega
    have hn_pos : 0 < n := hperf.2
    have hm_pos : 0 < m := by
      by_contra hcon
      have hm0 : m = 0 := by omega
      rw [hm0, zero_pow two_ne_zero, mul_zero] at hnm
      omega
    have hcop_pow : (q ^ e).Coprime (m ^ 2) := hcop.pow e 2
    have hsigma_mul : (ArithmeticFunction.sigma 1) (q ^ e * m ^ 2)
        = (ArithmeticFunction.sigma 1) (q ^ e) * (ArithmeticFunction.sigma 1) (m ^ 2) :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop_pow
    have hsigma_n : (ArithmeticFunction.sigma 1) (q ^ e)
        * (ArithmeticFunction.sigma 1) (m ^ 2) = 2 * (q ^ e * m ^ 2) := by
      rw [← hsigma_mul, ← hnm, ArithmeticFunction.sigma_one_apply]
      exact (Nat.perfect_iff_sum_divisors_eq_two_mul hn_pos).mp hperf
    have hS_sum : (ArithmeticFunction.sigma 1) (q ^ e)
        = ∑ k ∈ Finset.range (e + 1), q ^ k :=
      ArithmeticFunction.sigma_one_apply_prime_pow hq
    have hS_split : (ArithmeticFunction.sigma 1) (q ^ e)
        = 1 + q * (∑ k ∈ Finset.range e, q ^ k) := by
      rw [hS_sum, Finset.sum_range_succ']
      have hpow : ∀ k ∈ Finset.range e, q ^ (k + 1) = q * q ^ k :=
        fun k _ => pow_succ' q k
      rw [Finset.sum_congr rfl hpow, ← Finset.mul_sum, pow_zero, add_comm]
    have hS_cop : ((ArithmeticFunction.sigma 1) (q ^ e)).Coprime (q ^ e) := by
      have hq1 : Nat.Coprime q (1 + q * (∑ k ∈ Finset.range e, q ^ k)) :=
        (Nat.coprime_add_mul_left_right q 1 _).mpr (Nat.coprime_one_right q)
      have hSq : ((ArithmeticFunction.sigma 1) (q ^ e)).Coprime q := by
        rw [hS_split]
        exact hq1.symm
      simpa using hSq.pow 1 e
    have hS_dvd : (ArithmeticFunction.sigma 1) (q ^ e) ∣ q ^ e * (2 * m ^ 2) :=
      ⟨(ArithmeticFunction.sigma 1) (m ^ 2), by rw [hsigma_n]; ring⟩
    have hS_dvd2 : (ArithmeticFunction.sigma 1) (q ^ e) ∣ 2 * m ^ 2 :=
      hS_cop.dvd_of_dvd_mul_left hS_dvd
    have hS_le : (ArithmeticFunction.sigma 1) (q ^ e) ≤ 2 * m ^ 2 :=
      Nat.le_of_dvd (by have h2 : 0 < m ^ 2 := pow_pos hm_pos 2; omega) hS_dvd2
    have hSq_lt : q ^ e < (ArithmeticFunction.sigma 1) (q ^ e) := by
      rw [hS_sum, Finset.sum_range_succ]
      have hmem : 0 ∈ Finset.range e := Finset.mem_range.mpr (by omega)
      have h1 : 1 ≤ ∑ k ∈ Finset.range e, q ^ k := by
        have hle := Finset.single_le_sum (s := Finset.range e) (f := fun k => q ^ k)
          (fun i _ => Nat.zero_le _) hmem
        simpa using hle
      omega
    have hq5 : q ^ 5 ≤ q ^ e := Nat.pow_le_pow_right hq.pos he5
    calc q ^ 5 ≤ q ^ e := hq5
      _ < (ArithmeticFunction.sigma 1) (q ^ e) := hSq_lt
      _ ≤ 2 * m ^ 2 := hS_le

end MetaMathlibExt
