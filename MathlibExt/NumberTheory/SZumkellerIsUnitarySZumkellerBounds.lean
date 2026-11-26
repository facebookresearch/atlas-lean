/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FieldSimp
public import MathlibExt.NumberTheory.SZumkeller
import MathlibExt.NumberTheory.UnitaryDivisorCount

/-!
# Lower bounds for unitary s-Zumkeller numbers

## Main statements

* `sum_sq_unitaryDivisors`: the sum of the squares of the unitary divisors of `n ≠ 0` is
  `∏ p ∈ n.primeFactors, (1 + p ^ (2 * n.factorization p))` (Lemma 3(i)).
* `isUnitarySZumkeller_bounds`: a unitary s-Zumkeller number satisfies three lower bounds in
  terms of its least unitary divisor above `1`, proved from the product formula
  (Proposition 11).

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The complementary divisor of a unitary divisor is a unitary divisor. -/
private theorem div_mem_unitaryDivisors {n d : ℕ} (h : d ∈ Nat.unitaryDivisors n) :
    n / d ∈ Nat.unitaryDivisors n := by
  obtain ⟨hdvd, hn0, hcop⟩ := Nat.mem_unitaryDivisors.mp h
  have hdiv : n / (n / d) = d := Nat.div_div_self hdvd hn0
  refine Nat.mem_unitaryDivisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hn0, ?_⟩
  rw [hdiv]
  exact hcop.symm

/-- Every positive integer is its own unitary divisor. -/
private theorem self_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) :
    n ∈ Nat.unitaryDivisors n := by
  refine Nat.mem_unitaryDivisors.mpr ⟨dvd_rfl, hn, ?_⟩
  rw [Nat.div_self (Nat.pos_of_ne_zero hn)]
  exact Nat.coprime_one_right n

/-- Reindexing a sum over unitary divisors by complementary divisors. -/
private theorem sum_comp_div_unitaryDivisors (n : ℕ) (hn : n ≠ 0) (f : ℕ → ℚ) :
    ∑ d ∈ Nat.unitaryDivisors n, f (n / d) = ∑ d ∈ Nat.unitaryDivisors n, f d := by
  refine Finset.sum_bij (fun d _ => n / d) (fun d hd => div_mem_unitaryDivisors hd) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ h
    have e₁ := Nat.div_div_self (Nat.dvd_of_mem_unitaryDivisors ha₁) hn
    have e₂ := Nat.div_div_self (Nat.dvd_of_mem_unitaryDivisors ha₂) hn
    rw [h] at e₁
    exact e₁.symm.trans e₂
  · intro b hb
    exact ⟨n / b, div_mem_unitaryDivisors hb,
      Nat.div_div_self (Nat.dvd_of_mem_unitaryDivisors hb) hn⟩
  · intro a _
    rfl

/-- **Sum of squares of unitary divisors.** For every positive integer $n$, the sum of the
squares of the unitary divisors of $n$ equals $\prod_{p} \left(1 + p^{2k_p}\right)$, where $p$
ranges over the distinct prime factors of $n$ and $k_p$ is the exponent of $p$ in $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 3(i) (quoting Subbarao and
Warren). -/
public theorem sum_sq_unitaryDivisors (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ Nat.unitaryDivisors n, d ^ 2 =
      ∏ p ∈ n.primeFactors, (1 + p ^ (2 * n.factorization p)) := by
  rw [sum_unitaryDivisors_eq_sum_powerset n hn (fun d => d ^ 2), Finset.prod_one_add]
  refine Finset.sum_congr rfl fun s _ => ?_
  show (∏ p ∈ s, p ^ n.factorization p) ^ 2 = _
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_mul, mul_comm (n.factorization p) 2]

/-- The product formula for the sum of squared unitary divisors, over `ℚ`. -/
private theorem sum_sq_unitaryDivisors_rat (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2 =
      ∏ p ∈ n.primeFactors, (1 + ((p : ℚ) ^ n.factorization p) ^ 2) := by
  have h := sum_sq_unitaryDivisors n hn
  have hcast : ((∑ d ∈ Nat.unitaryDivisors n, d ^ 2 : ℕ) : ℚ) =
      ∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2 := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Nat.cast_pow]
  rw [← hcast, h, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  congr 1
  have hexp : 2 * n.factorization p = n.factorization p * 2 :=
    Nat.mul_comm _ _
  rw [hexp, pow_mul]

/-- **Lower bounds for unitary s-Zumkeller numbers.** Let $n$ be a unitary s-Zumkeller
number, let $q$ be the least unitary divisor of $n$ greater than $1$, and for each prime $p$
dividing $n$ let $k_p$ be the exponent of $p$ in $n$. Then, with both sums over all unitary
divisors $d$ of $n$ (including $n$ itself), $n^2 (2/q^2 + 1) \le \sum_d d^2$ and
$2/q^2 + 1 \le \sum_d 1/d^2$. Moreover $2/q^2 + 1 \le \prod_{p \mid n} (1 + p^{2k_p})/p^{2k_p}$,
the product running over the primes $p$ dividing $n$.

The number $q$ is the smallest of the prime powers $p^{k_p}$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 11. -/
public theorem isUnitarySZumkeller_bounds (n q : ℕ) (h : IsUnitarySZumkeller n)
    (hq : IsLeast {d | d ∈ Nat.unitaryDivisors n ∧ 1 < d} q) :
    (n : ℚ) ^ 2 * (2 / (q : ℚ) ^ 2 + 1) ≤ ∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2 ∧
      2 / (q : ℚ) ^ 2 + 1 ≤ ∑ d ∈ Nat.unitaryDivisors n, 1 / (d : ℚ) ^ 2 ∧
      2 / (q : ℚ) ^ 2 + 1 ≤
        ∏ p ∈ n.primeFactors,
          (1 + ((p : ℚ) ^ n.factorization p) ^ 2) / ((p : ℚ) ^ n.factorization p) ^ 2 := by
  obtain ⟨A, hAsub, hAne, hBne, hbal⟩ := h
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Nat.unitaryDivisors_zero, Finset.erase_empty] at hAsub
    have hA0 := Finset.subset_empty.mp hAsub
    rw [hA0] at hAne
    exact Finset.not_nonempty_empty hAne
  have hqmem : q ∈ Nat.unitaryDivisors n ∧ 1 < q := hq.1
  have hq1 : 1 < q := hqmem.2
  have hqdvd : q ∣ n := Nat.dvd_of_mem_unitaryDivisors hqmem.1
  have hqn0 : q ≠ 0 := by omega
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqn0
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hmem : n / q ∈ (Nat.unitaryDivisors n).erase n := by
    rw [Finset.mem_erase]
    exact ⟨ne_of_lt (Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hq1),
      div_mem_unitaryDivisors hqmem.1⟩
  have hsumB : ∑ d ∈ (Nat.unitaryDivisors n).erase n \ A, (d : ℚ) ^ 2 =
      ∑ d ∈ A, (d : ℚ) ^ 2 := by
    exact_mod_cast hbal.symm
  have hT : (((n / q : ℕ)) : ℚ) ^ 2 ≤ ∑ d ∈ A, (d : ℚ) ^ 2 := by
    by_cases hm : n / q ∈ A
    · exact Finset.single_le_sum (fun d _ => sq_nonneg _) hm
    · have hmB : n / q ∈ (Nat.unitaryDivisors n).erase n \ A :=
        Finset.mem_sdiff.mpr ⟨hmem, hm⟩
      have hle := Finset.single_le_sum (s := (Nat.unitaryDivisors n).erase n \ A)
        (f := fun d : ℕ => (d : ℚ) ^ 2) (fun d _ => sq_nonneg _) hmB
      rw [hsumB] at hle
      exact hle
  have hErase : ∑ d ∈ (Nat.unitaryDivisors n).erase n, (d : ℚ) ^ 2 =
      2 * ∑ d ∈ A, (d : ℚ) ^ 2 := by
    have hsd := Finset.sum_sdiff (f := fun d : ℕ => (d : ℚ) ^ 2) hAsub
    rw [hsumB] at hsd
    linarith
  have hTotal : ∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2 =
      2 * ∑ d ∈ A, (d : ℚ) ^ 2 + (n : ℚ) ^ 2 := by
    have hse := Finset.sum_erase_add (Nat.unitaryDivisors n)
      (fun d : ℕ => (d : ℚ) ^ 2) (self_mem_unitaryDivisors hn0)
    rw [hErase] at hse
    linarith
  have hdiv : (((n / q : ℕ)) : ℚ) = (n : ℚ) / (q : ℚ) := Nat.cast_div hqdvd hq0
  have hfield : (n : ℚ) ^ 2 * (2 / (q : ℚ) ^ 2 + 1) =
      2 * (((n / q : ℕ)) : ℚ) ^ 2 + (n : ℚ) ^ 2 := by
    rw [hdiv]
    field_simp
  have hP1 : (n : ℚ) ^ 2 * (2 / (q : ℚ) ^ 2 + 1) ≤
      ∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2 := by
    rw [hfield, hTotal]
    linarith [hT]
  have hInv : ∑ d ∈ Nat.unitaryDivisors n, 1 / (d : ℚ) ^ 2 =
      (∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2) / (n : ℚ) ^ 2 := by
    calc ∑ d ∈ Nat.unitaryDivisors n, 1 / (d : ℚ) ^ 2
        = ∑ d ∈ Nat.unitaryDivisors n, 1 / (((n / d : ℕ)) : ℚ) ^ 2 :=
          (sum_comp_div_unitaryDivisors n hn0 _).symm
      _ = ∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2 / (n : ℚ) ^ 2 := by
          refine Finset.sum_congr rfl fun d hd => ?_
          have hddvd : d ∣ n := Nat.dvd_of_mem_unitaryDivisors hd
          have hd0 : (d : ℚ) ≠ 0 := by
            have hdn0 : d ≠ 0 := by
              rintro rfl
              rw [zero_dvd_iff] at hddvd
              exact hn0 hddvd
            exact_mod_cast hdn0
          rw [Nat.cast_div hddvd hd0]
          field_simp
      _ = (∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2) / (n : ℚ) ^ 2 :=
          (Finset.sum_div _ _ _).symm
  have hP2 : 2 / (q : ℚ) ^ 2 + 1 ≤ ∑ d ∈ Nat.unitaryDivisors n, 1 / (d : ℚ) ^ 2 := by
    rw [hInv]
    have hpos : 0 < (n : ℚ) ^ 2 := by positivity
    rw [le_div_iff₀ hpos, mul_comm]
    exact hP1
  have hnsq : (n : ℚ) ^ 2 =
      ∏ p ∈ n.primeFactors, (((p : ℚ) ^ n.factorization p)) ^ 2 := by
    have hfactor : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization hn0
    calc (n : ℚ) ^ 2 = (∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p) ^ 2 := by
            rw [hfactor]
      _ = ∏ p ∈ n.primeFactors, ((p : ℚ) ^ n.factorization p) ^ 2 :=
          (Finset.prod_pow _ _ _).symm
  have hProdEq : ∑ d ∈ Nat.unitaryDivisors n, 1 / (d : ℚ) ^ 2 =
      ∏ p ∈ n.primeFactors,
        (1 + ((p : ℚ) ^ n.factorization p) ^ 2) / ((p : ℚ) ^ n.factorization p) ^ 2 := by
    rw [hInv, sum_sq_unitaryDivisors_rat n hn0, hnsq, Finset.prod_div_distrib]
  have hP3 : 2 / (q : ℚ) ^ 2 + 1 ≤ ∏ p ∈ n.primeFactors,
      (1 + ((p : ℚ) ^ n.factorization p) ^ 2) / ((p : ℚ) ^ n.factorization p) ^ 2 := by
    rw [← hProdEq]
    exact hP2
  exact ⟨hP1, hP2, hP3⟩

end

end MetaMathlibExt
