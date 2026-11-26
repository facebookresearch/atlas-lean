/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Tauto
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.SZumkeller

/-!
# Properties of even s-Zumkeller numbers

`MetaMathlibExt.isSZumkeller_even_props` proves the parity and prime-factor properties
and the lower bound for the sum of squared divisors in Proposition 1 of Jayanta Kalita
and Helen K. Saikia, *A Study on Generalized Zumkeller Numbers*.
-/

namespace MetaMathlibExt

private theorem even_sum_range_pow_mul_two_iff (p k : ℕ) :
    Even (∑ i ∈ Finset.range (k + 1), p ^ (i * 2)) ↔ Odd p ∧ Odd k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.even_add', Nat.odd_pow_iff (by omega),
      ← Nat.not_even_iff_odd, ih, Nat.odd_add_one]
    tauto

/-- **Properties of even s-Zumkeller numbers.** Let $n$ be an even s-Zumkeller number and let
$\sigma_2(n)$ be the sum of the squares of the positive divisors of $n$. Then $\sigma_2(n)$ is
even, some odd prime $p$ divides $n$ with an odd exponent in the prime factorization of $n$, and
$3n^2 \le 2\sigma_2(n)$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 1. -/
public theorem isSZumkeller_even_props (n : ℕ) (h : IsSZumkeller n) (he : Even n) :
    Even (ArithmeticFunction.sigma 2 n) ∧
      (∃ p ∈ n.primeFactors, Odd p ∧ Odd (n.factorization p)) ∧
      3 * n ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n := by
  obtain ⟨A, hA, hne, hcomp, hbal⟩ := h
  have hn : 0 < n := zero_lt_one.trans (Nat.nonempty_properDivisors.mp (hne.mono hA))
  have hσ : ArithmeticFunction.sigma 2 n = n ^ 2 + ∑ d ∈ n.properDivisors, d ^ 2 := by
    rw [ArithmeticFunction.sigma_apply, ← Nat.insert_self_properDivisors hn.ne',
      Finset.sum_insert Nat.self_notMem_properDivisors]
  have hsplit := Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hA
  have hEven : Even (ArithmeticFunction.sigma 2 n) := by
    rw [hσ, ← hsplit, ← hbal]
    exact (he.pow_of_ne_zero (by decide)).add ⟨∑ d ∈ A, d ^ 2, rfl⟩
  refine ⟨hEven, ?_, ?_⟩
  · have hprod := hEven.two_dvd
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn.ne']
      at hprod
    obtain ⟨p, hp, hfactor⟩ := Nat.prime_two.prime.exists_mem_finset_dvd hprod
    exact ⟨p, hp, (even_sum_range_pow_mul_two_iff p (n.factorization p)).mp
      (even_iff_two_dvd.mpr hfactor)⟩
  · obtain ⟨S, _, hS⟩ := (isSZumkeller_iff_of_even n hn he).mp ⟨A, hA, hne, hcomp, hbal⟩
    have hnonneg : 0 ≤ ∑ d ∈ S, (d : ℤ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact_mod_cast (show 3 * (n : ℤ) ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n by omega)

end MetaMathlibExt
