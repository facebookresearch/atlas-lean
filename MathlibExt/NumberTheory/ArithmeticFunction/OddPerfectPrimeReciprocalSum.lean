/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.BigOperators
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndexDiv

/-!
# Bound on H(n) for primitive non-deficient numbers

This file proves `exists_abundancySup_le_two_add_div_minFac`: there is a real
constant `C` such that every primitive non-deficient number `n` with least prime
factor `p₁` satisfies `H(n) ≤ 2 + C/p₁`, where `H(n)` is `abundancySup`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59
(arXiv:2402.14234v5), Proposition 8.
-/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

namespace MetaMathlibExt

-- Preliminary: primitive non-deficient implies n ≥ 2
private theorem two_le_of_prim (n : ℕ) (hn : IsPrimitiveNondeficient n) : 2 ≤ n := by
  obtain ⟨⟨hn0, hsum⟩, _⟩ := hn
  by_contra h
  have hlt : n < 2 := lt_of_not_ge h
  have h01 : n = 0 ∨ n = 1 := by omega
  rcases h01 with rfl | rfl
  · exact absurd rfl hn0
  · have h1 : ∑ d ∈ Nat.divisors 1, d = 1 := by decide
    omega

-- minFac is prime and in primeFactors
private theorem minFac_mem (n : ℕ) (hn2 : 2 ≤ n) : n.minFac ∈ n.primeFactors := by
  have hn1 : n ≠ 1 := by omega
  have hprime : n.minFac.Prime := Nat.minFac_prime hn1
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hn0 : n ≠ 0 := by omega
  exact Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hn0⟩

private theorem minFac_ge_two (n : ℕ) (hn2 : 2 ≤ n) : 2 ≤ n.minFac := by
  have hn1 : n ≠ 1 := by omega
  exact (Nat.minFac_prime hn1).two_le

private theorem minFac_le_of_mem (n p : ℕ) (hp : p ∈ n.primeFactors) : n.minFac ≤ p := by
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  exact Nat.minFac_le_of_dvd hprime.two_le hdvd

private theorem factor_pos (n p : ℕ) (hn0 : n ≠ 0) (hp : p ∈ n.primeFactors) :
    0 < n.factorization p := by
  have h := Nat.mem_primeFactors.mp hp
  exact Nat.Prime.factorization_pos_of_dvd h.1 hn0 h.2.1

-- 1 ≤ abundancyIndex for positive n
private theorem one_le_abund (n : ℕ) (hn : 0 < n) : 1 ≤ abundancyIndex n := by
  rw [abundancyIndex, one_le_div (by exact_mod_cast hn)]
  exact_mod_cast Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn.ne')

-- abundancyIndex of proper deficient divisor is < 2
private theorem abund_lt_two_of_def (m : ℕ) (hm0 : m ≠ 0)
    (hdef : ∑ d ∈ Nat.divisors m, d < 2 * m) : abundancyIndex m < 2 := by
  have hmR : (0 : ℚ) < (m : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
  rw [abundancyIndex, div_lt_iff₀ hmR]
  have hcast : ((∑ d ∈ Nat.divisors m, d : ℕ) : ℚ) < ((2 * m : ℕ) : ℚ) := by
    exact_mod_cast hdef
  push_cast at hcast ⊢
  linarith

-- n / p is a proper divisor
private theorem div_mem_divisors (n p : ℕ) (hn0 : n ≠ 0) (hpdvd : p ∣ n) :
    n / p ∈ Nat.divisors n :=
  Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hpdvd, hn0⟩

private theorem div_lt_self_of_dvd (n p : ℕ) (hn : 0 < n) (hp1 : 1 < p) : n / p < n :=
  Nat.div_lt_self hn hp1

private theorem div_pos_of_dvd (n p : ℕ) (hn : 0 < n) (hpdvd : p ∣ n) (hp0 : 0 < p) :
    0 < n / p :=
  Nat.div_pos (Nat.le_of_dvd hn hpdvd) hp0

-- p^a ≥ p for a ≥ 1
private theorem pow_ge_self (p a : ℕ) (hp : 2 ≤ p) (ha : 1 ≤ a) : p ≤ p ^ a := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  simp only [Nat.add_comm 1 b, pow_succ]
  have hb : 1 ≤ p ^ b := Nat.one_le_pow b p (by omega)
  calc p = p * 1 := (mul_one p).symm
    _ ≤ p * p ^ b := Nat.mul_le_mul_left p hb
    _ = p ^ b * p := mul_comm _ _

-- Main h bound: h(n) < 2 + 2/p1
private theorem abund_lt (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    abundancyIndex n < 2 + 2 / (n.minFac : ℚ) := by
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  obtain ⟨⟨hn0, hsum⟩, hprim⟩ := hn
  have hn_pos : 0 < n := by omega
  have hp1_mem : n.minFac ∈ n.primeFactors := minFac_mem n hn2
  have hp1_prime : n.minFac.Prime := Nat.prime_of_mem_primeFactors hp1_mem
  have hp1_ge2 : 2 ≤ n.minFac := hp1_prime.two_le
  have hpdvd : n.minFac ∣ n := Nat.dvd_of_mem_primeFactors hp1_mem
  have ha_pos : 0 < n.factorization n.minFac := factor_pos n n.minFac hn0 hp1_mem
  have ha1 : 1 ≤ n.factorization n.minFac := ha_pos
  have hdiv_mem : n / n.minFac ∈ Nat.divisors n := div_mem_divisors n n.minFac hn0 hpdvd
  have hdiv_lt : n / n.minFac < n := div_lt_self_of_dvd n n.minFac hn_pos hp1_prime.one_lt
  have hdiv_pos : 0 < n / n.minFac := div_pos_of_dvd n n.minFac hn_pos hpdvd hp1_prime.pos
  have hdef := hprim _ hdiv_mem hdiv_lt
  have hdiv_ne : n / n.minFac ≠ 0 := by omega
  have h_small : abundancyIndex (n / n.minFac) < 2 :=
    abund_lt_two_of_def _ hdiv_ne hdef
  have h_big_pos : 0 < abundancyIndex (n / n.minFac) :=
    zero_lt_one.trans_le (one_le_abund _ hdiv_pos)
  have hratio := abundancyIndex_div_le n n.minFac (n.factorization n.minFac)
    hn_pos hp1_prime ha1 rfl
  have hpow_ge : n.minFac ≤ n.minFac ^ n.factorization n.minFac :=
    pow_ge_self _ _ hp1_ge2 ha1
  have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by exact_mod_cast hp1_prime.pos
  have hpowQ_ge : (n.minFac : ℚ) ≤ ((n.minFac ^ n.factorization n.minFac : ℕ) : ℚ) := by
    exact_mod_cast hpow_ge
  have hpowQ_eq : ((n.minFac ^ n.factorization n.minFac : ℕ) : ℚ) =
      (n.minFac : ℚ) ^ n.factorization n.minFac := by push_cast; ring
  -- h(n) = (h(n)/h(n/p)) * h(n/p)
  have h_eq : abundancyIndex n =
      (abundancyIndex n / abundancyIndex (n / n.minFac)) *
        abundancyIndex (n / n.minFac) := by
    field_simp
  rw [h_eq]
  have h1 : abundancyIndex n / abundancyIndex (n / n.minFac) ≤
      1 + 1 / (n.minFac : ℚ) ^ n.factorization n.minFac := hratio
  have h2 : (1 : ℚ) + 1 / (n.minFac : ℚ) ^ n.factorization n.minFac ≤
      1 + 1 / (n.minFac : ℚ) := by
    have hle : (1 : ℚ) / (n.minFac : ℚ) ^ n.factorization n.minFac ≤ 1 / (n.minFac : ℚ) := by
      rw [← hpowQ_eq]
      exact one_div_le_one_div_of_le hp1Q_pos hpowQ_ge
    linarith
  have h_ratio_le : abundancyIndex n / abundancyIndex (n / n.minFac) ≤
      1 + 1 / (n.minFac : ℚ) := h1.trans h2
  have h_nonneg : 0 ≤ abundancyIndex n / abundancyIndex (n / n.minFac) := by
    apply div_nonneg _ (le_of_lt h_big_pos)
    exact le_trans zero_le_one (one_le_abund _ hn_pos)
  -- (ratio) * h(n/p) < (1+1/p1) * 2
  have hpos2 : (0 : ℚ) < 1 + 1 / (n.minFac : ℚ) := by positivity
  have h_bound : (abundancyIndex n / abundancyIndex (n / n.minFac)) *
      abundancyIndex (n / n.minFac) < (1 + 1 / (n.minFac : ℚ)) * 2 := by
    have hstep1 : (abundancyIndex n / abundancyIndex (n / n.minFac)) *
        abundancyIndex (n / n.minFac) ≤ (1 + 1 / (n.minFac : ℚ)) *
        abundancyIndex (n / n.minFac) :=
      mul_le_mul_of_nonneg_right h_ratio_le (le_of_lt h_big_pos)
    have hstep2 : (1 + 1 / (n.minFac : ℚ)) * abundancyIndex (n / n.minFac) <
        (1 + 1 / (n.minFac : ℚ)) * 2 :=
      mul_lt_mul_of_pos_left h_small hpos2
    exact lt_of_le_of_lt hstep1 hstep2
  calc (abundancyIndex n / abundancyIndex (n / n.minFac)) *
        abundancyIndex (n / n.minFac)
      < (1 + 1 / (n.minFac : ℚ)) * 2 := h_bound
    _ = 2 + 2 / (n.minFac : ℚ) := by ring

-- h < 3 corollary
private theorem abund_lt_three (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    abundancyIndex n < 3 := by
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  have hp1_ge2 : 2 ≤ n.minFac := minFac_ge_two n hn2
  have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hp1Q_ge : (2 : ℚ) ≤ (n.minFac : ℚ) := by exact_mod_cast hp1_ge2
  have h1 : (2 : ℚ) / (n.minFac : ℚ) ≤ 1 := by
    rw [div_le_one hp1Q_pos]
    linarith
  have h2 := abund_lt n hn
  linarith

-- 1 + sum ≤ prod (1 + .) for nonnegative f
private theorem one_add_sum_le_prod (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ p ∈ s, 0 ≤ f p) : 1 + ∑ p ∈ s, f p ≤ ∏ p ∈ s, (1 + f p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat IH =>
    have hf_a : 0 ≤ f a := hf a (Finset.mem_insert_self a t)
    have hf_t : ∀ p ∈ t, 0 ≤ f p := fun p hp => hf p (Finset.mem_insert_of_mem hp)
    have hIH := IH hf_t
    have hprod_ge_one : (1 : ℚ) ≤ ∏ p ∈ t, (1 + f p) := by
      apply Finset.one_le_prod₀
      intro p hp
      linarith [hf_t p hp]
    have hfa_le : f a ≤ (∏ p ∈ t, (1 + f p)) * f a := by
      have : (1 : ℚ) * f a ≤ (∏ p ∈ t, (1 + f p)) * f a :=
        mul_le_mul_of_nonneg_right hprod_ge_one hf_a
      simpa using this
    rw [Finset.sum_insert hat, Finset.prod_insert hat]
    have h_add := add_le_add hIH hfa_le
    have h_eq1 : (1 + ∑ p ∈ t, f p) + f a = 1 + (f a + ∑ p ∈ t, f p) := by ring
    have h_eq2 : (∏ p ∈ t, (1 + f p)) + (∏ p ∈ t, (1 + f p)) * f a =
        (1 + f a) * (∏ p ∈ t, (1 + f p)) := by ring
    rw [h_eq1, h_eq2] at h_add
    exact h_add

-- h as a product over prime factors
private theorem abund_eq_prod (n : ℕ) (hn : n ≠ 0) :
    abundancyIndex n = ∏ p ∈ n.primeFactors,
      (((∑ k ∈ Finset.range (n.factorization p + 1), p ^ k : ℕ)) : ℚ) /
        (p : ℚ) ^ n.factorization p := by
  have hprod : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  rw [abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn, hprod]
  simp only [mul_one, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib]

-- Each factor is at least 1 + 1/p
private theorem factor_ge_one_add (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    (1 : ℚ) + 1 / (p : ℚ) ≤
      (((∑ k ∈ Finset.range (a + 1), p ^ k : ℕ)) : ℚ) / (p : ℚ) ^ a := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  simp only [Nat.add_comm 1 b] at ha ⊢
  -- a = b + 1, so range (b+2) contains b and b+1
  have hpQ_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have hpow_pos : (0 : ℚ) < (p : ℚ) ^ (b + 1) := pow_pos hpQ_pos _
  have hpow_ne : (p : ℚ) ^ (b + 1) ≠ 0 := ne_of_gt hpow_pos
  have hpb_ne : (p : ℚ) ^ b ≠ 0 := pow_ne_zero _ (ne_of_gt hpQ_pos)
  -- sum in ℕ is at least p^(b+1) + p^b
  have hsum_ge : p ^ (b + 1) + p ^ b ≤ ∑ k ∈ Finset.range (b + 1 + 1), p ^ k := by
    have hsub : ({b, b + 1} : Finset ℕ) ⊆ Finset.range (b + 1 + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => Nat.zero_le (p ^ i))
    have hsum_pair : ∑ k ∈ ({b, b + 1} : Finset ℕ), p ^ k = p ^ b + p ^ (b + 1) := by
      rw [Finset.sum_pair (by omega)]
    rw [hsum_pair] at hle
    linarith [hle]
  have hcast : ((p ^ (b + 1) + p ^ b : ℕ) : ℚ) ≤
      ((∑ k ∈ Finset.range (b + 1 + 1), p ^ k : ℕ) : ℚ) := by
    exact_mod_cast hsum_ge
  push_cast at hcast ⊢
  rw [le_div_iff₀ hpow_pos]
  -- goal: (1 + 1/p) * p^(b+1) ≤ sum; have p^(b+1) + p^b ≤ sum
  have h_alg : (1 + 1 / (p : ℚ)) * (p : ℚ) ^ (b + 1) =
      (p : ℚ) ^ (b + 1) + (p : ℚ) ^ b := by
    field_simp
    rw [pow_succ]
    ring
  rw [h_alg]
  exact hcast

-- Product of (1+1/p) is at most h(n)
private theorem prod_le_abund (n : ℕ) (hn0 : n ≠ 0) :
    ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ)) ≤ abundancyIndex n := by
  rw [abund_eq_prod n hn0]
  apply Finset.prod_le_prod₀ _ _
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpQ_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hprime.pos
    positivity
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha : 1 ≤ n.factorization p := factor_pos n p hn0 hp
    exact factor_ge_one_add p _ hprime ha

-- T(n) = sum 1/p is less than 2
private theorem sum_inv_lt_two (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) < 2 := by
  have h3 : abundancyIndex n < 3 := abund_lt_three n hn
  obtain ⟨⟨hn0, hsum⟩, hprim⟩ := hn
  have h1 : (1 : ℚ) + ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ≤
      ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ)) := by
    apply one_add_sum_le_prod
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpQ_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hprime.pos
    positivity
  have h2 : ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ)) ≤ abundancyIndex n :=
    prod_le_abund n hn0
  linarith

-- H/h as a product (copied from AbundancySupDivIndex)
private def primePowerRatio (p k : ℕ) : ℚ := (p : ℚ) ^ k / ((p : ℚ) ^ k - 1)

private theorem ratio_eq_prod {n : ℕ} (hn : n ≠ 0) :
    abundancySup n / abundancyIndex n =
      ∏ p ∈ n.primeFactors, primePowerRatio p (n.factorization p + 1) := by
  have hprod : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  rw [abundancyIndex, abundancySup, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn, hprod]
  simp only [mul_one, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [div_div_div_eq, mul_geom_sum, ← pow_succ', primePowerRatio]

-- p^(a+1) ≥ 4 for prime p and a ≥ 1
private theorem pow_succ_ge_four (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    4 ≤ p ^ (a + 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : p ^ 2 ≤ p ^ (a + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
  norm_num at h2 ⊢
  linarith [h1, h2]

-- primePowerRatio = 1 + 1/(p^k - 1)
private theorem ratio_eq_one_add (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) :
    primePowerRatio p k = 1 + 1 / ((p : ℚ) ^ k - 1) := by
  have hpQ : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hlt : (1 : ℚ) < (p : ℚ) ^ k := one_lt_pow₀ hpQ (by omega)
  have hne : (p : ℚ) ^ k - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
  rw [primePowerRatio]
  field_simp
  ring

-- y_p = 1/(p^(a+1) - 1) is nonnegative
private theorem y_nonneg (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    0 ≤ (1 : ℚ) / ((p : ℚ) ^ (a + 1) - 1) := by
  have hpQ : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hlt : (1 : ℚ) < (p : ℚ) ^ (a + 1) := one_lt_pow₀ hpQ (by omega)
  have hpos : (0 : ℚ) < (p : ℚ) ^ (a + 1) - 1 := sub_pos.mpr hlt
  positivity

-- y_p ≤ 2 / p^(a+1)
private theorem y_le_two_div_pow (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    (1 : ℚ) / ((p : ℚ) ^ (a + 1) - 1) ≤ 2 / (p : ℚ) ^ (a + 1) := by
  have hpQ : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hX : (2 : ℚ) ≤ (p : ℚ) ^ (a + 1) := by
    have h4 : (4 : ℚ) ≤ (p : ℚ) ^ (a + 1) := by
      have h4n : 4 ≤ p ^ (a + 1) := pow_succ_ge_four p a hp ha
      have hcast : ((4 : ℕ) : ℚ) ≤ ((p ^ (a + 1) : ℕ) : ℚ) := by exact_mod_cast h4n
      push_cast at hcast ⊢
      linarith [hcast]
    linarith
  have hpos : (0 : ℚ) < (p : ℚ) ^ (a + 1) - 1 := by linarith
  have hposX : (0 : ℚ) < (p : ℚ) ^ (a + 1) := by linarith
  rw [div_le_div_iff₀ hpos hposX]
  nlinarith [hX]

-- p^(a+1) ≥ p^2
private theorem pow_succ_ge_sq (p a : ℕ) (hp : 1 ≤ p) (ha : 1 ≤ a) :
    (p : ℚ) ^ 2 ≤ (p : ℚ) ^ (a + 1) := by
  apply pow_le_pow_right₀ (by exact_mod_cast hp) (by omega)

-- 2/p^(a+1) ≤ 2/p^2
private theorem two_div_pow_le (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    (2 : ℚ) / (p : ℚ) ^ (a + 1) ≤ 2 / (p : ℚ) ^ 2 := by
  have hpQ : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.one_le
  have hle : (p : ℚ) ^ 2 ≤ (p : ℚ) ^ (a + 1) := pow_succ_ge_sq p a hp.one_le ha
  have hpos2 : (0 : ℚ) < (p : ℚ) ^ 2 := by positivity
  apply div_le_div_of_nonneg_left (by norm_num) hpos2 hle

-- 1/p^2 ≤ (1/p1)*(1/p) for p ≥ p1
private theorem inv_sq_le (p p1 : ℕ) (hp : p.Prime) (hle : p1 ≤ p) (hp1 : 2 ≤ p1) :
    (1 : ℚ) / (p : ℚ) ^ 2 ≤ (1 / (p1 : ℚ)) * (1 / (p : ℚ)) := by
  have hpQ_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have hp1Q_pos : (0 : ℚ) < (p1 : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hleQ : (p1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hle
  have h_inv_le : (1 : ℚ) / (p : ℚ) ≤ 1 / (p1 : ℚ) :=
    one_div_le_one_div_of_le hp1Q_pos hleQ
  have h_nonneg : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
  have h_eq : (1 : ℚ) / (p : ℚ) ^ 2 = (1 / (p : ℚ)) * (1 / (p : ℚ)) := by
    rw [div_mul_div_comm]
    simp [pow_two]
  rw [h_eq]
  exact mul_le_mul_of_nonneg_right h_inv_le h_nonneg

-- Sum of 1/p^2 is at most T/p1
private theorem sum_inv_sq_le (n : ℕ) (hn2 : 2 ≤ n) :
    ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ^ 2 ≤
      (1 / (n.minFac : ℚ)) * ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hle : n.minFac ≤ p := minFac_le_of_mem n p hp
  have hp1 : 2 ≤ n.minFac := minFac_ge_two n hn2
  exact inv_sq_le p n.minFac hprime hle hp1

-- Sum of y is less than 4/p1
private theorem sum_y_lt (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) <
      4 / (n.minFac : ℚ) := by
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  have hT := sum_inv_lt_two n hn
  have hsq := sum_inv_sq_le n hn2
  have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by
    have h2 := minFac_ge_two n hn2
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  -- Each y ≤ 2/p^2
  have h_each : ∀ p ∈ n.primeFactors,
      (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) ≤ 2 / (p : ℚ) ^ 2 := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha : 1 ≤ n.factorization p := by
      have hn0 : n ≠ 0 := by omega
      exact factor_pos n p hn0 hp
    exact (y_le_two_div_pow p _ hprime ha).trans (two_div_pow_le p _ hprime ha)
  have h_sum_le : ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) ≤
      ∑ p ∈ n.primeFactors, (2 : ℚ) / (p : ℚ) ^ 2 :=
    Finset.sum_le_sum h_each
  have h_sum_eq : ∑ p ∈ n.primeFactors, (2 : ℚ) / (p : ℚ) ^ 2 =
      2 * ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [h_sum_eq] at h_sum_le
  have h_bound : (2 : ℚ) * ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ^ 2 <
      4 / (n.minFac : ℚ) := by
    have h1 : ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ^ 2 <
        (1 / (n.minFac : ℚ)) * 2 := by
      have h_nonneg : (0 : ℚ) ≤ 1 / (n.minFac : ℚ) := by positivity
      have h_strict : (1 / (n.minFac : ℚ)) * ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) <
          (1 / (n.minFac : ℚ)) * 2 :=
        mul_lt_mul_of_pos_left hT (by positivity)
      exact lt_of_le_of_lt hsq h_strict
    have h2 : (2 : ℚ) * ∑ p ∈ n.primeFactors, (1 : ℚ) / (p : ℚ) ^ 2 <
        2 * ((1 / (n.minFac : ℚ)) * 2) :=
      mul_lt_mul_of_pos_left h1 (by norm_num)
    have h_eq : (2 : ℚ) * ((1 / (n.minFac : ℚ)) * 2) = 4 / (n.minFac : ℚ) := by ring
    rw [h_eq] at h2
    exact h2
  exact lt_of_le_of_lt h_sum_le h_bound

-- Product bound for small sums: if sum ≤ 1/2 then prod (1+y) ≤ 1 + 2*sum
private theorem prod_le_one_add_two_mul (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ p ∈ s, 0 ≤ f p) (hsum : ∑ p ∈ s, f p ≤ 1 / 2) :
    ∏ p ∈ s, (1 + f p) ≤ 1 + 2 * ∑ p ∈ s, f p := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat IH =>
    have hf_a : 0 ≤ f a := hf a (Finset.mem_insert_self a t)
    have hf_t : ∀ p ∈ t, 0 ≤ f p := fun p hp => hf p (Finset.mem_insert_of_mem hp)
    rw [Finset.sum_insert hat] at hsum
    have hsum_t : ∑ p ∈ t, f p ≤ 1 / 2 := by linarith [hf_a]
    have hIH := IH hf_t hsum_t
    have h_nonneg : (0 : ℚ) ≤ 1 + f a := by linarith
    have h_mul_le : (1 + f a) * ∏ p ∈ t, (1 + f p) ≤
        (1 + f a) * (1 + 2 * ∑ p ∈ t, f p) :=
      mul_le_mul_of_nonneg_left hIH h_nonneg
    rw [Finset.prod_insert hat]
    -- (1+f a)*(1+2∑_t) = 1 + 2∑_t + f a + 2 f a ∑_t ≤ 1 + 2(∑_t + f a)
    have h_key : (1 + f a) * (1 + 2 * ∑ p ∈ t, f p) ≤
        1 + 2 * (f a + ∑ p ∈ t, f p) := by
      have h2sum : 2 * ∑ p ∈ t, f p ≤ 1 := by linarith
      have hfa_mul : f a * (2 * ∑ p ∈ t, f p) ≤ f a * 1 :=
        mul_le_mul_of_nonneg_left h2sum hf_a
      nlinarith [hfa_mul, hf_a]
    have h_eq : (1 : ℚ) + 2 * (f a + ∑ p ∈ t, f p) = 1 + 2 * ∑ p ∈ insert a t, f p := by
      rw [Finset.sum_insert hat]
    rw [h_eq] at h_key
    exact h_mul_le.trans h_key

-- H/h = prod (1 + y)
private theorem ratio_eq_prod_one_add (n : ℕ) (hn0 : n ≠ 0) :
    abundancySup n / abundancyIndex n =
      ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℚ) ^ (n.factorization p + 1) - 1)) := by
  rw [ratio_eq_prod hn0]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have ha : 1 ≤ n.factorization p := factor_pos n p hn0 hp
  have hk : 2 ≤ n.factorization p + 1 := by omega
  exact ratio_eq_one_add p _ hprime hk

-- Large p1 case: H < 2 + 34/p1 in ℚ
private theorem abund_sup_lt_large (n : ℕ) (hn : IsPrimitiveNondeficient n)
    (h8 : 8 ≤ n.minFac) : abundancySup n < 2 + 34 / (n.minFac : ℚ) := by
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  obtain ⟨⟨hn0, hsum⟩, hprim⟩ := hn
  have hn_pos : 0 < n := by omega
  have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hp1Q_ge8 : (8 : ℚ) ≤ (n.minFac : ℚ) := by exact_mod_cast h8
  have hp1Q_ge1 : (1 : ℚ) ≤ (n.minFac : ℚ) := by linarith
  -- hne for H = h * (H/h)
  have hne : abundancyIndex n ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (one_le_abund _ hn_pos))
  have hH : abundancySup n =
      abundancyIndex n * (abundancySup n / abundancyIndex n) := by
    field_simp
  -- H/h = prod (1+y)
  have h_ratio_eq := ratio_eq_prod_one_add n hn0
  -- sum y < 4/p1 ≤ 1/2
  have h_sum_lt : ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) <
      4 / (n.minFac : ℚ) := by
    have hn' : IsPrimitiveNondeficient n := ⟨⟨hn0, hsum⟩, hprim⟩
    exact sum_y_lt n hn'
  have h4_le : (4 : ℚ) / (n.minFac : ℚ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp1Q_pos (by norm_num)]
    linarith
  have h_sum_le : ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) ≤
      1 / 2 :=
    le_of_lt (lt_of_lt_of_le h_sum_lt h4_le)
  have h_y_nonneg : ∀ p ∈ n.primeFactors,
      0 ≤ (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha : 1 ≤ n.factorization p := factor_pos n p hn0 hp
    exact y_nonneg p _ hprime ha
  have h_prod_le : ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℚ) ^ (n.factorization p + 1) - 1)) ≤
      1 + 2 * ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) :=
    prod_le_one_add_two_mul _ _ h_y_nonneg h_sum_le
  rw [← h_ratio_eq] at h_prod_le
  -- H/h < 1 + 8/p1
  have h_ratio_lt : abundancySup n / abundancyIndex n < 1 + 8 / (n.minFac : ℚ) := by
    have h1 : (1 : ℚ) + 2 * ∑ p ∈ n.primeFactors,
        (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) < 1 + 8 / (n.minFac : ℚ) := by
      have h2 : (2 : ℚ) * ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) <
          8 / (n.minFac : ℚ) := by
        have h3 : (2 : ℚ) * ∑ p ∈ n.primeFactors,
            (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) < 2 * (4 / (n.minFac : ℚ)) :=
          mul_lt_mul_of_pos_left h_sum_lt (by norm_num)
        have h_eq : (2 : ℚ) * (4 / (n.minFac : ℚ)) = 8 / (n.minFac : ℚ) := by ring
        rw [h_eq] at h3
        exact h3
      linarith
    exact lt_of_le_of_lt h_prod_le h1
  -- h < 2 + 2/p1
  have hn' : IsPrimitiveNondeficient n := ⟨⟨hn0, hsum⟩, hprim⟩
  have h_h_lt : abundancyIndex n < 2 + 2 / (n.minFac : ℚ) := abund_lt n hn'
  have h_h_nonneg : (0 : ℚ) ≤ abundancyIndex n :=
    le_trans zero_le_one (one_le_abund _ hn_pos)
  have h_ratio_nonneg : (0 : ℚ) ≤ abundancySup n / abundancyIndex n := by
    rw [h_ratio_eq]
    apply Finset.prod_nonneg
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha : 1 ≤ n.factorization p := factor_pos n p hn0 hp
    have hy := y_nonneg p _ hprime ha
    linarith
  have h_pos2 : (0 : ℚ) < 2 + 2 / (n.minFac : ℚ) := by positivity
  -- H = h*(H/h) < (2+2/p1)*(1+8/p1) ≤ 2+34/p1
  rw [hH]
  have h_step1 : abundancyIndex n * (abundancySup n / abundancyIndex n) ≤
      (2 + 2 / (n.minFac : ℚ)) * (abundancySup n / abundancyIndex n) :=
    mul_le_mul_of_nonneg_right (le_of_lt h_h_lt) h_ratio_nonneg
  have h_step2 : (2 + 2 / (n.minFac : ℚ)) * (abundancySup n / abundancyIndex n) <
      (2 + 2 / (n.minFac : ℚ)) * (1 + 8 / (n.minFac : ℚ)) :=
    mul_lt_mul_of_pos_left h_ratio_lt h_pos2
  have h_prod_bound : (2 + 2 / (n.minFac : ℚ)) * (1 + 8 / (n.minFac : ℚ)) ≤
      2 + 34 / (n.minFac : ℚ) := by
    have hpos : (0 : ℚ) < (n.minFac : ℚ) := hp1Q_pos
    field_simp
    nlinarith [hp1Q_ge1]
  exact lt_of_lt_of_le (lt_of_le_of_lt h_step1 h_step2) h_prod_bound

-- Uniform bound: (H:ℝ) < 27 for all primitive n
private theorem abund_sup_lt_unif (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    (abundancySup n : ℝ) < 27 := by
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  obtain ⟨⟨hn0, hsum⟩, hprim⟩ := hn
  have hn_pos : 0 < n := by omega
  have hn' : IsPrimitiveNondeficient n := ⟨⟨hn0, hsum⟩, hprim⟩
  have h_h_lt3Q : abundancyIndex n < 3 := abund_lt_three n hn'
  have h_h_lt3R : (abundancyIndex n : ℝ) < 3 := by exact_mod_cast h_h_lt3Q
  have h_h_nonnegR : (0 : ℝ) ≤ (abundancyIndex n : ℝ) := by
    have h1 : (1 : ℚ) ≤ abundancyIndex n := one_le_abund _ hn_pos
    have h2 : (1 : ℝ) ≤ (abundancyIndex n : ℝ) := by exact_mod_cast h1
    linarith
  have h_sum_lt4 : ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) <
      4 / (n.minFac : ℚ) := sum_y_lt n hn'
  have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by
    have h2 := minFac_ge_two n hn2
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hp1Q_ge2 : (2 : ℚ) ≤ (n.minFac : ℚ) := by
    have h2 := minFac_ge_two n hn2
    exact_mod_cast h2
  have h4_le2 : (4 : ℚ) / (n.minFac : ℚ) ≤ 2 := by
    rw [div_le_iff₀ hp1Q_pos]
    linarith
  have h_sum_lt2Q : ∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) < 2 :=
    lt_of_lt_of_le h_sum_lt4 h4_le2
  have h_ratio_eqQ := ratio_eq_prod_one_add n hn0
  have h_ratioR_eq : ((abundancySup n / abundancyIndex n : ℚ) : ℝ) =
      ∏ p ∈ n.primeFactors, (1 + 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) := by
    rw [h_ratio_eqQ, Rat.cast_prod]
    apply Finset.prod_congr rfl
    intro p _
    push_cast
    ring
  have h_each_le : ∀ p ∈ n.primeFactors,
      (1 : ℝ) + 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1) ≤
        Real.exp (1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) := by
    intro p _
    have h := Real.add_one_le_exp (1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1))
    linarith
  have h_z_nonneg : ∀ p ∈ n.primeFactors,
      (0 : ℝ) ≤ 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.one_lt
    have ha : 1 ≤ n.factorization p := factor_pos n p hn0 hp
    have hlt : (1 : ℝ) < (p : ℝ) ^ (n.factorization p + 1) := one_lt_pow₀ hpr (by omega)
    have hpos : (0 : ℝ) < (p : ℝ) ^ (n.factorization p + 1) - 1 := sub_pos.mpr hlt
    positivity
  have h_each_nonneg : ∀ p ∈ n.primeFactors,
      (0 : ℝ) ≤ (1 : ℝ) + 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1) := by
    intro p hp
    have hz := h_z_nonneg p hp
    linarith
  have h_prod_le_exp : ∏ p ∈ n.primeFactors,
      ((1 : ℝ) + 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) ≤
      ∏ p ∈ n.primeFactors, Real.exp (1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) :=
    Finset.prod_le_prod₀ h_each_nonneg h_each_le
  have h_prod_exp_eq : ∏ p ∈ n.primeFactors,
      Real.exp (1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) =
      Real.exp (∑ p ∈ n.primeFactors, 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) := by
    rw [Real.exp_sum]
  have h_sumR_lt2 : (∑ p ∈ n.primeFactors, 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) < 2 := by
    have h_cast_eq : (∑ p ∈ n.primeFactors, 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) =
        ((∑ p ∈ n.primeFactors, (1 : ℚ) / ((p : ℚ) ^ (n.factorization p + 1) - 1) : ℚ) : ℝ) := by
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro p _
      push_cast
      ring
    rw [h_cast_eq]
    exact_mod_cast h_sum_lt2Q
  have h_exp_lt : Real.exp (∑ p ∈ n.primeFactors, 1 / (((p : ℝ) ^ (n.factorization p + 1)) - 1)) <
      Real.exp 2 := by
    apply Real.exp_lt_exp.mpr
    exact h_sumR_lt2
  have h_exp2_lt9 : Real.exp (2 : ℝ) < 9 := by
    have h1 : Real.exp (1 : ℝ) < 3 := Real.exp_one_lt_three
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h_eq : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
      have : (2 : ℝ) = 1 + 1 := by norm_num
      rw [this, Real.exp_add]
    rw [h_eq]
    nlinarith [h1, hpos]
  have h_ratioR_lt9 : ((abundancySup n / abundancyIndex n : ℚ) : ℝ) < 9 := by
    rw [h_ratioR_eq]
    exact lt_of_le_of_lt (h_prod_le_exp.trans_eq h_prod_exp_eq) (lt_trans h_exp_lt h_exp2_lt9)
  have h_ratioR_nonneg : (0 : ℝ) ≤ ((abundancySup n / abundancyIndex n : ℚ) : ℝ) := by
    rw [h_ratioR_eq]
    apply Finset.prod_nonneg
    intro p hp
    exact h_each_nonneg p hp
  have hH_eq : (abundancySup n : ℝ) =
      (abundancyIndex n : ℝ) * ((abundancySup n / abundancyIndex n : ℚ) : ℝ) := by
    have hne : abundancyIndex n ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le (one_le_abund _ hn_pos))
    have hQ : abundancySup n = abundancyIndex n * (abundancySup n / abundancyIndex n) := by
      field_simp
    have hcast : ((abundancySup n : ℚ) : ℝ) =
        ((abundancyIndex n * (abundancySup n / abundancyIndex n) : ℚ) : ℝ) :=
      congrArg _ hQ
    rw [hcast]
    push_cast
    ring
  rw [hH_eq]
  have h_step1 : (abundancyIndex n : ℝ) * ((abundancySup n / abundancyIndex n : ℚ) : ℝ) ≤
      3 * ((abundancySup n / abundancyIndex n : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_right (le_of_lt h_h_lt3R) h_ratioR_nonneg
  have h_step2 : (3 : ℝ) * ((abundancySup n / abundancyIndex n : ℚ) : ℝ) < 3 * 9 :=
    mul_lt_mul_of_pos_left h_ratioR_lt9 (by norm_num)
  have h_eq : (3 : ℝ) * 9 = 27 := by norm_num
  rw [h_eq] at h_step2
  exact lt_of_le_of_lt h_step1 h_step2

/-- **Bound on $H(n)$ for primitive non-deficient numbers by the least prime factor.** For a
positive integer $n$ write $H(n) = \prod_{p \mid n} p/(p-1)$, the product over the prime
divisors of $n$. There is a real constant $C$ such that every primitive non-deficient number
$n$ with least prime factor $p_1$ satisfies $H(n) \le 2 + C/p_1$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 8 (`integers-2025-A59-prop-8`). -/
public theorem exists_abundancySup_le_two_add_div_minFac :
    ∃ C : ℝ, ∀ n : ℕ, IsPrimitiveNondeficient n →
      (abundancySup n : ℝ) ≤ 2 + C / n.minFac := by
  use 200
  intro n hn
  have hn2 : 2 ≤ n := two_le_of_prim n hn
  have hp1_ge2 : 2 ≤ n.minFac := minFac_ge_two n hn2
  by_cases h8 : 8 ≤ n.minFac
  · -- Large case: H < 2+34/p1 in ℚ, so ≤ 2+200/p1 in ℝ
    have hQ : abundancySup n < 2 + 34 / (n.minFac : ℚ) := abund_sup_lt_large n hn h8
    have hp1Q_pos : (0 : ℚ) < (n.minFac : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have h_le_Q : (2 : ℚ) + 34 / (n.minFac : ℚ) ≤ 2 + 200 / (n.minFac : ℚ) := by
      have h1 : (34 : ℚ) / (n.minFac : ℚ) ≤ 200 / (n.minFac : ℚ) := by
        have hpos := hp1Q_pos
        field_simp
        norm_num
      linarith
    have h_lt_Q : abundancySup n < 2 + 200 / (n.minFac : ℚ) := lt_of_lt_of_le hQ h_le_Q
    have h_cast_lt : ((abundancySup n : ℚ) : ℝ) < ((2 + 200 / (n.minFac : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast h_lt_Q
    have h_cast_eq : ((2 + 200 / (n.minFac : ℚ) : ℚ) : ℝ) = 2 + 200 / (n.minFac : ℝ) := by
      push_cast
      ring
    rw [h_cast_eq] at h_cast_lt
    exact le_of_lt h_cast_lt
  · -- Small case: H < 27 ≤ 2+200/p1
    have h8lt : n.minFac < 8 := by omega
    have h_unif : (abundancySup n : ℝ) < 27 := abund_sup_lt_unif n hn
    have hmin_le7 : n.minFac ≤ 7 := by omega
    have hR_pos : (0 : ℝ) < (n.minFac : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hR_le7 : (n.minFac : ℝ) ≤ 7 := by exact_mod_cast hmin_le7
    have h25 : (25 : ℝ) ≤ 200 / (n.minFac : ℝ) := by
      rw [le_div_iff₀ hR_pos]
      nlinarith [hR_le7]
    have h27 : (27 : ℝ) ≤ 2 + 200 / (n.minFac : ℝ) := by linarith
    exact le_of_lt (lt_of_lt_of_le h_unif h27)

end MetaMathlibExt
