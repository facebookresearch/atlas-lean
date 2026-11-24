/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.UnitaryDivisor

/-!
# s-Zumkeller numbers

An s-Zumkeller number admits an equal-squares partition of its proper divisors.
For a positive even number, removing its half from the part containing it gives
a subset-sum criterion for such a partition.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **s-Zumkeller numbers.** A natural number $n$ is s-Zumkeller if its proper divisors can be
split into two disjoint nonempty sets whose elements have equal sums of squares. Each of the two
sums is then $(\sigma_2(n) - n^2)/2$, where $\sigma_2(n)$ is the sum of the squares of the
positive divisors of $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Definition 1. -/
def IsSZumkeller (n : ℕ) : Prop :=
  ∃ A ⊆ n.properDivisors, A.Nonempty ∧ (n.properDivisors \ A).Nonempty ∧
    ∑ d ∈ A, d ^ 2 = ∑ d ∈ n.properDivisors \ A, d ^ 2

/-- **Unitary s-Zumkeller numbers.** A natural number $n$ is a unitary s-Zumkeller number when
its proper unitary divisors (the unitary divisors of $n$ other than $n$) split into two nonempty
disjoint sets $A$ and $B$ with equal sums of squares, $\sum_{d \in A} d^2 = \sum_{d \in B} d^2$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Definition 2. -/
def IsUnitarySZumkeller (n : ℕ) : Prop :=
  ∃ A ⊆ (Nat.unitaryDivisors n).erase n, A.Nonempty ∧
    ((Nat.unitaryDivisors n).erase n \ A).Nonempty ∧
    ∑ d ∈ A, d ^ 2 = ∑ d ∈ (Nat.unitaryDivisors n).erase n \ A, d ^ 2

/-- **$60$ is s-Zumkeller.** The number $60$ is s-Zumkeller: the squares of its proper divisors
$1, 2, 5, 30$ sum to $1^2 + 2^2 + 5^2 + 30^2 = 930$, which is half of the sum of the squares of
all proper divisors of $60$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Example 1. -/
theorem isSZumkeller_sixty : IsSZumkeller 60 :=
  ⟨{1, 2, 5, 30}, by decide, by decide, by decide, by decide⟩

/-- **The number 6 is not s-Zumkeller.** The number $6$ is not an s-Zumkeller number: the squares of
its proper divisors sum to $1^2 + 2^2 + 3^2 = 14$, and they admit no split into two parts with
equal sums.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Section 1. -/
theorem not_isSZumkeller_six : ¬ IsSZumkeller 6 := by
  unfold IsSZumkeller
  decide

/-- **The number 60 is unitary s-Zumkeller.** The number $60$ is a unitary s-Zumkeller number: its
proper unitary divisors are $1, 3, 4, 5, 12, 15, 20$, and $20^2 + 3^2 + 1^2 = 410$ is half the sum
of their squares.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Example 2. -/
theorem isUnitarySZumkeller_sixty : IsUnitarySZumkeller 60 :=
  ⟨{1, 3, 20}, by decide, by decide, by decide, by decide⟩

/-- **The number 6 is not unitary s-Zumkeller.** The number $6$ is not a unitary s-Zumkeller
number.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Section 1. -/
theorem not_isUnitarySZumkeller_six : ¬ IsUnitarySZumkeller 6 := by
  unfold IsUnitarySZumkeller
  decide

/-- **Criterion for even s-Zumkeller numbers.** Let $n$ be an even positive integer and let
$\sigma_2(n)$ be the sum of the squares of the positive divisors of $n$. Then $n$ is s-Zumkeller
if and only if there is a (possibly empty) set $S$ of proper divisors of $n$, not containing
$n/2$, such that $4 \sum_{d \in S} d^2 = 2\sigma_2(n) - 3n^2$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 2. -/
theorem isSZumkeller_iff_of_even (n : ℕ) (hn : 0 < n) (he : Even n) :
    IsSZumkeller n ↔
      ∃ S ⊆ n.properDivisors.erase (n / 2),
        4 * (∑ d ∈ S, d ^ 2 : ℤ) = 2 * ArithmeticFunction.sigma 2 n - 3 * n ^ 2 := by
  let k := n / 2
  have hk : k ∈ n.properDivisors := Nat.mem_properDivisors.mpr
    ⟨Nat.div_dvd_of_dvd he.two_dvd, Nat.div_lt_self hn (by decide)⟩
  have hsq : k ^ 2 * 4 = n ^ 2 := by
    calc
      k ^ 2 * 4 = (k * 2) ^ 2 := by norm_num [mul_pow]
      _ = n ^ 2 := by rw [show k * 2 = n from Nat.div_mul_cancel he.two_dvd]
  have hσ : ArithmeticFunction.sigma 2 n = n ^ 2 + ∑ d ∈ n.properDivisors, d ^ 2 := by
    rw [ArithmeticFunction.sigma_apply, ← Nat.insert_self_properDivisors hn.ne',
      Finset.sum_insert Nat.self_notMem_properDivisors]
  constructor
  · rintro ⟨A, hA, _, _, hbal⟩
    -- Choose the part containing k, exchanging the two parts if necessary.
    obtain ⟨B, hB, hkB, hsum⟩ : ∃ B ⊆ n.properDivisors, k ∈ B ∧
        ∑ d ∈ B, d ^ 2 = ∑ d ∈ n.properDivisors \ B, d ^ 2 := by
      by_cases h : k ∈ A
      · exact ⟨A, hA, h, hbal⟩
      · exact ⟨_, Finset.sdiff_subset, Finset.mem_sdiff.mpr ⟨hk, h⟩, by
          rwa [Finset.sdiff_sdiff_eq_self hA, eq_comm]⟩
    refine ⟨B.erase k, Finset.erase_subset_erase k hB, ?_⟩
    rw [eq_sub_iff_add_eq]
    have hsplit := Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hB
    have herase := B.sum_erase_add (fun d => d ^ 2) hkB
    exact_mod_cast (show 4 * (∑ d ∈ B.erase k, d ^ 2) + 3 * n ^ 2 =
      2 * ArithmeticFunction.sigma 2 n by omega)
  · rintro ⟨S, hS, hsum⟩
    have hkS : k ∉ S := Finset.notMem_mono hS (Finset.notMem_erase k _)
    have hA := Finset.insert_subset hk (hS.trans (Finset.erase_subset k n.properDivisors))
    rw [eq_sub_iff_add_eq] at hsum
    have hsum' : 4 * (∑ d ∈ S, d ^ 2) + 3 * n ^ 2 = 2 * ArithmeticFunction.sigma 2 n := by
      exact_mod_cast hsum
    have hsplit := Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hA
    have hbal : ∑ d ∈ insert k S, d ^ 2 = ∑ d ∈ n.properDivisors \ insert k S, d ^ 2 := by
      rw [Finset.sum_insert hkS] at hsplit ⊢
      omega
    refine ⟨insert k S, hA, Finset.insert_nonempty _ _, ?_, hbal⟩
    apply Finset.nonempty_of_sum_ne_zero (f := fun d : ℕ => d ^ 2)
    rw [← hbal, Finset.sum_insert hkS]
    have := Nat.pos_of_mem_properDivisors hk
    positivity

open Finset in
private theorem three_dvd_of_isSZumkeller.sum_inv_sq_lt (n : ℕ) (h₃ : ¬ 3 ∣ n) :
    ∑ d ∈ n.divisors, ((d : ℚ) ^ 2)⁻¹ < 3 / 2 := by
  -- Below 10 we can exclude 3, 6 and 9. The entire tail contributes at most 1/9.
  let small := (Icc 1 9).filter (fun d : ℕ => ¬ 3 ∣ d)
  let tail := Ioc 9 (max 9 n)
  have hsub : n.divisors ⊆ small ∪ tail := by
    intro d hd
    simp only [small, tail, mem_union, mem_filter, mem_Icc, mem_Ioc]
    by_cases h : d ≤ 9
    · exact Or.inl ⟨⟨Nat.pos_of_mem_divisors hd, h⟩,
        fun h₃d => h₃ (h₃d.trans (Nat.dvd_of_mem_divisors hd))⟩
    · exact Or.inr ⟨Nat.lt_of_not_ge h, (Nat.divisor_le hd).trans (le_max_right _ _)⟩
  have hdisj : Disjoint small tail := by
    apply disjoint_left.mpr
    intro d hd ht
    simp only [small, tail, mem_filter, mem_Icc, mem_Ioc] at hd ht
    exact ht.1.not_ge hd.1.2
  have htail : ∑ d ∈ tail, ((d : ℚ) ^ 2)⁻¹ ≤ 1 / 9 := by
    refine (sum_Ioc_inv_sq_le_sub (α := ℚ) (by decide : 9 ≠ 0) (le_max_left 9 n)).trans ?_
    simp [one_div]
  calc
    _ ≤ ∑ d ∈ small ∪ tail, ((d : ℚ) ^ 2)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = (∑ d ∈ small, ((d : ℚ) ^ 2)⁻¹) + ∑ d ∈ tail, ((d : ℚ) ^ 2)⁻¹ := sum_union hdisj
    _ ≤ (∑ d ∈ small, ((d : ℚ) ^ 2)⁻¹) + 1 / 9 := add_le_add_right htail _
    _ < 3 / 2 := by decide +kernel

/-- **Even s-Zumkeller numbers are divisible by 3.** If $n$ is an even s-Zumkeller number, then
$3$ divides $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 4. -/
theorem three_dvd_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n) (he : Even n) :
    3 ∣ n := by
  by_contra h₃
  have hn : 0 < n := Nat.pos_of_ne_zero fun h₀ => h₃ (h₀ ▸ dvd_zero 3)
  obtain ⟨S, _, hS⟩ := (isSZumkeller_iff_of_even n hn he).mp h
  have hnonneg : 0 ≤ ∑ d ∈ S, (d : ℤ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlower : 3 * (n : ℚ) ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n := by
    exact_mod_cast (show 3 * (n : ℤ) ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n by omega)
  -- Pair each divisor d with n / d to express the normalized sum as reciprocal squares.
  have hupper : (ArithmeticFunction.sigma 2 n : ℚ) < (n : ℚ) ^ 2 * (3 / 2) := calc
    _ = (n : ℚ) ^ 2 * ∑ d ∈ n.divisors, ((d : ℚ) ^ 2)⁻¹ := by
      rw [ArithmeticFunction.sigma_eq_sum_div, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_pow, Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd), div_pow, div_eq_mul_inv]
    _ < _ := mul_lt_mul_of_pos_left (three_dvd_of_isSZumkeller.sum_inv_sq_lt n h₃) (by positivity)
  linarith

set_option linter.unusedVariables false in
/-- **Harmonic mean of squared divisors of s-Zumkeller numbers $2^\alpha(2^{\alpha+1}-1)$.** Let
$\alpha \ge 1$ be an integer, let $n = 2^\alpha (2^{\alpha+1} - 1)$ and let $\tau(n)$ be the
number of positive divisors of $n$. If $n$ is s-Zumkeller, then
$\tau(n) / \sum_{d \mid n} d^{-2} < 2^{2\alpha+3}/3$, where the sum runs over the positive
divisors $d$ of $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 10. -/
theorem harmonicMeanSq_lt_of_isSZumkeller_mersenne (α n : ℕ) (hα : 1 ≤ α)
    (hn : n = 2 ^ α * (2 ^ (α + 1) - 1)) (h : IsSZumkeller n) :
    (n.divisors.card : ℚ) / ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 < 2 ^ (2 * α + 3) / 3 := by
  obtain ⟨A, hA, hne, _, _⟩ := h
  have hn₀ : n ≠ 0 := (Nat.nonempty_properDivisors.mp (hne.mono hA)).ne_zero
  have hsum : 1 ≤ ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 := calc
    1 = 1 / (1 : ℚ) ^ 2 := by norm_num
    _ ≤ _ := Finset.single_le_sum (f := fun d : ℕ => 1 / (d : ℚ) ^ 2)
      (fun d _ => div_nonneg zero_le_one (sq_nonneg _)) (Nat.one_mem_divisors.mpr hn₀)
  have hsize : n ≤ 2 ^ (2 * α + 1) := calc
    n ≤ 2 ^ α * 2 ^ (α + 1) := hn ▸ Nat.mul_le_mul_left _ (Nat.sub_le ..)
    _ = 2 ^ (2 * α + 1) := by rw [← pow_add, two_mul, Nat.add_assoc]
  calc
    _ ≤ (n.divisors.card : ℚ) := div_le_self (by positivity) hsum
    _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
    _ ≤ 2 ^ (2 * α + 1) := by exact_mod_cast hsize
    _ < _ := by
      rw [show 2 * α + 3 = (2 * α + 1) + 2 by omega, pow_add (2 : ℚ) _ 2,
        lt_div_iff₀ (by norm_num)]
      exact mul_lt_mul_of_pos_left (by norm_num : (3 : ℚ) < 2 ^ 2) (by positivity)

/-- **Product formulas for the sum of divisors.** Let $n \ne 0$ be a natural number, let
$\sigma(n)$ be the sum of the divisors of $n$, and for each prime $p$ dividing $n$ let $k_p$ be
the exponent of $p$ in $n$. Then, with products over the primes $p$ dividing $n$,
$$\sigma(n) = \prod_{p \mid n} \frac{p^{k_p + 1} - 1}{p - 1}$$
and
$$\frac{\sigma(n)}{n} = \prod_{p \mid n} \frac{p^{k_p + 1} - 1}{p^{k_p} (p - 1)}.$$
If moreover $n > 1$, then $\sigma(n)/n < \prod_{p \mid n} p/(p - 1)$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 1(i) (quoting Peng and
Bhaskara Rao). -/
public theorem sigma_one_prod_formulas (n : ℕ) (hn : n ≠ 0) :
    (ArithmeticFunction.sigma 1 n : ℚ) =
        ∏ p ∈ n.primeFactors, ((p : ℚ) ^ (n.factorization p + 1) - 1) / (p - 1) ∧
      (ArithmeticFunction.sigma 1 n : ℚ) / n =
        ∏ p ∈ n.primeFactors,
          ((p : ℚ) ^ (n.factorization p + 1) - 1) / ((p : ℚ) ^ n.factorization p * (p - 1)) ∧
      (1 < n →
        (ArithmeticFunction.sigma 1 n : ℚ) / n < ∏ p ∈ n.primeFactors, (p : ℚ) / (p - 1)) := by
  have hprime (p : ℕ) (hp : p ∈ n.primeFactors) : (1 : ℚ) < p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hsum : (ArithmeticFunction.sigma 1 n : ℚ) =
      ∏ p ∈ n.primeFactors, ((p : ℚ) ^ (n.factorization p + 1) - 1) / (p - 1) := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn,
      Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    simpa only [Nat.cast_sum, Nat.cast_pow, mul_one] using
      (geom_sum_eq (ne_of_gt (hprime p hp)) (n.factorization p + 1))
  have hfactor : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn)
  have hratio : (ArithmeticFunction.sigma 1 n : ℚ) / n =
      ∏ p ∈ n.primeFactors,
        ((p : ℚ) ^ (n.factorization p + 1) - 1) / ((p : ℚ) ^ n.factorization p * (p - 1)) := by
    rw [hsum, hfactor, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun _ _ => by rw [div_div, mul_comm]
  refine ⟨hsum, hratio, fun hn₁ => ?_⟩
  rw [hratio]
  have hnnonempty : n.primeFactors.Nonempty := by
    by_contra hnempty
    have he := Finset.not_nonempty_iff_eq_empty.mp hnempty
    rw [he, Finset.prod_empty] at hfactor
    exact (show (1 : ℚ) < n by exact_mod_cast hn₁).ne' hfactor
  apply Finset.prod_lt_prod_of_nonempty₀ _ _ hnnonempty
  · intro p hp
    have hp₁ := hprime p hp
    have hp₀ : (0 : ℚ) < p := zero_lt_one.trans hp₁
    exact div_pos (sub_pos.mpr (one_lt_pow₀ hp₁ (Nat.succ_ne_zero _)))
      (mul_pos (pow_pos hp₀ _) (sub_pos.mpr hp₁))
  · intro p hp
    have hp₁ := hprime p hp
    have hpos : 0 < (p : ℚ) ^ n.factorization p := pow_pos (zero_lt_one.trans hp₁) _
    have hsub : 0 < (p : ℚ) - 1 := sub_pos.mpr hp₁
    calc
      _ < (p : ℚ) ^ (n.factorization p + 1) / ((p : ℚ) ^ n.factorization p * (p - 1)) :=
        div_lt_div_of_pos_right (sub_lt_self _ zero_lt_one) (mul_pos hpos hsub)
      _ = _ := by rw [pow_succ, mul_div_mul_left _ _ hpos.ne']

end

end MetaMathlibExt
