/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Dold congruences and prime powers

Zhang's prime-power criterion for divisibility of the Möbius transform of an integer sequence.
-/

namespace MetaMathlibExt

open Finset
open scoped ArithmeticFunction.Moebius

private def doldTransform (V : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, μ (n / d) * V d

-- The divisors of a coprime product with a prime power are uniquely d * p ^ i.
private lemma sum_divisors_mul_prime_pow (f : ℕ → ℤ) {a p : ℕ} (ha : a ≠ 0)
    (hp : p.Prime) (hap : a.Coprime p) (k : ℕ) :
    ∑ d ∈ (a * p ^ k).divisors, f d =
      ∑ d ∈ a.divisors, ∑ i ∈ range (k + 1), f (d * p ^ i) := by
  rw [← sum_product a.divisors (range (k + 1)) (fun x : ℕ × ℕ => f (x.1 * p ^ x.2))]
  symm
  refine sum_bij (fun x _ => x.1 * p ^ x.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    obtain ⟨hd, hi⟩ := mem_product.mp hx
    exact Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd) (pow_dvd_pow _ (by simpa using hi)),
        mul_ne_zero ha (pow_ne_zero _ hp.ne_zero)⟩
  · rintro ⟨d, i⟩ hx ⟨e, j⟩ hy h
    obtain ⟨hd, _⟩ := mem_product.mp hx
    obtain ⟨he, _⟩ := mem_product.mp hy
    have hd' := hap.coprime_dvd_left (Nat.dvd_of_mem_divisors hd)
    have he' := hap.coprime_dvd_left (Nat.dvd_of_mem_divisors he)
    have hde : d = e := dvd_antisymm
      ((hd'.pow_right j).dvd_of_dvd_mul_right (h ▸ dvd_mul_right d (p ^ i)))
      ((he'.pow_right i).dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right e (p ^ j)))
    subst e
    exact Prod.ext rfl (Nat.pow_right_injective hp.two_le
      (Nat.mul_left_cancel (Nat.pos_of_mem_divisors hd) h))
  · intro x hx
    obtain ⟨d, q, hd, hq, rfl⟩ := Nat.dvd_mul.mp (Nat.dvd_of_mem_divisors hx)
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hq
    exact ⟨(d, i), mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hd, ha⟩, mem_range.mpr (by omega)⟩,
      rfl⟩

-- Only the two largest exponents in the divisor survive in the Möbius transform.
private lemma doldTransform_mul_prime_pow_succ (V : ℕ → ℤ) {a p : ℕ} (ha : a ≠ 0)
    (hp : p.Prime) (hap : a.Coprime p) (k : ℕ) :
    doldTransform V (a * p ^ (k + 1)) =
      ∑ d ∈ a.divisors, μ (a / d) * (V (d * p ^ (k + 1)) - V (d * p ^ k)) := by
  rw [doldTransform, sum_divisors_mul_prime_pow _ ha hp hap]
  refine sum_congr rfl fun d hd => ?_
  have hdiv (i : ℕ) (hi : i ≤ k + 1) :
      a * p ^ (k + 1) / (d * p ^ i) = a / d * p ^ (k + 1 - i) := by
    rw [← Nat.div_mul_div_comm (Nat.dvd_of_mem_divisors hd) (pow_dvd_pow p hi),
      Nat.div_eq_of_eq_mul_left (pow_pos hp.pos _) (Nat.pow_sub_mul_pow p hi).symm]
  have hcop : (a / d).Coprime p :=
    hap.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
  have hzero : ∑ i ∈ range k, μ (a * p ^ (k + 1) / (d * p ^ i)) * V (d * p ^ i) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    have hi' : i < k := mem_range.mp hi
    rw [hdiv i (by omega), ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hcop.pow_right _), ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show k + 1 - i ≠ 1 by omega]
  rw [sum_range_succ, sum_range_succ, hzero, zero_add, hdiv k (by omega), hdiv (k + 1) le_rfl,
    Nat.add_sub_cancel_left, Nat.sub_self, pow_zero, mul_one, pow_one,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp, mul_neg_one, neg_mul, mul_sub, sub_eq_add_neg,
    add_comm]

private lemma sum_doldTransform (V : ℕ → ℤ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, doldTransform V d = V n := by
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := doldTransform V) (g := V)).mpr _ n hn
  intro d _
  exact Nat.sum_divisorsAntidiagonal' (fun x y => μ x * V y)

@[expose] public section

/-- **Dold congruences via prime-power congruences.** Let $(V(n))_{n \ge 1}$ be a sequence of
integers and let $\mu$ denote the Möbius function. Then
$V(n p^m) \equiv V(n p^{m-1}) \pmod{p^m}$ holds for all integers $n, m \ge 1$ and all primes $p$
if and only if $n$ divides $\sum_{d \mid n} \mu(n/d) V(d)$ for every integer $n \ge 1$.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 30 (`jis-2024-24.3.3-lem-30`). -/
public theorem prime_power_congruence_iff_dold (V : ℕ → ℤ) :
    (∀ n m p : ℕ, 1 ≤ n → 1 ≤ m → p.Prime →
        V (n * p ^ m) ≡ V (n * p ^ (m - 1)) [ZMOD (p : ℤ) ^ m]) ↔
      ∀ n : ℕ, 1 ≤ n →
        (n : ℤ) ∣ ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * V d := by
  change _ ↔ ∀ n : ℕ, 1 ≤ n → (n : ℤ) ∣ doldTransform V n
  constructor
  · intro h n hn
    have hn' : n ≠ 0 := by omega
    -- Check the divisibility at each prime separately, using its full exponent in n.
    rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p r hp hpr
    have hr := (hp.pow_dvd_iff_le_factorization hn').mp hpr
    let a := n / p ^ n.factorization p
    have ha : a ≠ 0 := (Nat.ordCompl_pos p hn').ne'
    have hap : a.Coprime p := (Nat.coprime_ordCompl hp hn').symm
    have he : n = a * p ^ n.factorization p := by
      rw [mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
    cases hk : n.factorization p with
    | zero => simp [show r = 0 by omega]
    | succ k =>
      rw [hk] at he
      rw [← Int.natCast_dvd, Nat.cast_pow]
      apply (pow_dvd_pow (p : ℤ) (show r ≤ k + 1 by omega)).trans
      rw [he, doldTransform_mul_prime_pow_succ V ha hp hap]
      refine Finset.dvd_sum fun d hd => dvd_mul_of_dvd_right ?_ _
      exact Int.modEq_iff_dvd.mp (h d (k + 1) p (Nat.pos_of_mem_divisors hd) (by omega) hp).symm
  · intro h n m p hn hm hp
    have hn' : n ≠ 0 := by omega
    obtain ⟨k, a, hap, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn' p hp.ne_one
    have ha := Nat.pos_of_ne_zero (right_ne_zero_of_mul hn')
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hap' : a.Coprime p := (hp.coprime_iff_not_dvd.mpr hap).symm
    have hindex (i : ℕ) : p ^ k * a * p ^ i = a * p ^ (k + i) := by
      rw [pow_add, ← mul_assoc, mul_comm a]
    simp only [Nat.add_sub_cancel, hindex, ← Nat.add_assoc]
    apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd]
    -- After inversion the two divisor sums differ only in the top p-power layer.
    rw [← sum_doldTransform V (Nat.mul_pos ha (pow_pos hp.pos _)),
      ← sum_doldTransform V (Nat.mul_pos ha (pow_pos hp.pos _)),
      sum_divisors_mul_prime_pow _ ha.ne' hp hap', sum_divisors_mul_prime_pow _ ha.ne' hp hap',
      ← sum_sub_distrib]
    refine Finset.dvd_sum fun d hd => ?_
    rw [sum_range_succ, add_sub_cancel_left]
    have hpow : (p : ℤ) ^ (j + 1) ∣ (↑(d * p ^ (k + j + 1)) : ℤ) := by
      exact_mod_cast (dvd_mul_of_dvd_right (pow_dvd_pow p (show j + 1 ≤ k + j + 1 by omega)) d)
    exact hpow.trans (h _ (Nat.mul_pos (Nat.pos_of_mem_divisors hd) (pow_pos hp.pos _)))

end

end MetaMathlibExt
