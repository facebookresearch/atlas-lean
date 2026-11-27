/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsup
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Bounds for Euler's totient and the sum of divisors
-/

namespace MetaMathlibExt

@[expose] public section

open Filter Finset

private lemma sum_inv_sq_le (s : Finset ℕ) (y : ℕ) (hy : 0 < y)
    (hs : ∀ n ∈ s, y < n) : ∑ n ∈ s, (n : ℝ)⁻¹ ^ 2 ≤ (y : ℝ)⁻¹ := by
  let b := max y (s.sup id)
  have hyb : y ≤ b := le_max_left ..
  have htel : ∀ b : ℕ, y ≤ b →
      ∑ n ∈ Ioc y b, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) = (y : ℝ)⁻¹ - (b : ℝ)⁻¹ := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [← insert_Ioc_right_eq_Ioc_add_one hb, sum_insert (by simp), ih]
      push_cast
      ring
  calc
    _ ≤ ∑ n ∈ s, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) := by
      refine sum_le_sum fun n hn ↦ ?_
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by linarith [hs n hn])
      have h : 0 < (n : ℝ) - 1 := by linarith
      have h' : 0 < (n : ℝ) := by linarith
      field_simp
      linarith
    _ ≤ ∑ n ∈ Ioc y b, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) := by
      refine sum_le_sum_of_subset_of_nonneg (fun n hn ↦ mem_Ioc.mpr
        ⟨hs n hn, (le_sup (f := id) hn).trans (le_max_right ..)⟩) ?_
      intro n hn _
      have hn1 : (1 : ℝ) < n := by
        exact_mod_cast (show 1 < n by linarith [(mem_Ioc.mp hn).1])
      exact sub_nonneg.mpr (inv_anti₀ (by linarith) (by linarith))
    _ ≤ _ := by rw [htel b hyb]; exact sub_le_self _ (by positivity)

private lemma prod_one_sub_inv_sq_ge (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (1 / 4 : ℝ) ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹ ^ 2) := by
  have hprod : ∀ t : Finset ℕ, (∀ p ∈ t, 2 ≤ p) →
      1 - ∑ p ∈ t, (p : ℝ)⁻¹ ^ 2 ≤ ∏ p ∈ t, (1 - (p : ℝ)⁻¹ ^ 2) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert p t hp ih =>
      intro h
      have ht : ∀ q ∈ t, 2 ≤ q := fun q hq ↦ h q (mem_insert_of_mem hq)
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast h p (mem_insert_self ..)
      have hpi : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
      have hpi' : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hc : 0 ≤ 1 - (p : ℝ)⁻¹ ^ 2 := by nlinarith
      rw [sum_insert hp, prod_insert hp]
      have hi := mul_le_mul_of_nonneg_left (ih ht) hc
      have hn : 0 ≤ ∑ q ∈ t, (q : ℝ)⁻¹ ^ 2 := sum_nonneg fun _ _ ↦ by positivity
      nlinarith [mul_nonneg (sq_nonneg (p : ℝ)⁻¹) hn]
  have hsum : ∑ p ∈ s, (p : ℝ)⁻¹ ^ 2 ≤ 3 / 4 := by
    have hbound := sum_inv_sq_le (s.erase 2) 2 (by decide)
      (fun p hp ↦ lt_of_le_of_ne (hs p (mem_erase.mp hp).2)
        (Ne.symm (mem_erase.mp hp).1))
    by_cases h : 2 ∈ s
    · rw [← sum_erase_add _ _ h]
      norm_num at hbound ⊢
      linarith
    · rw [erase_eq_of_notMem h] at hbound
      exact hbound.trans (by norm_num)
  exact (by linarith only [hsum] : (1 / 4 : ℝ) ≤ 1 - ∑ p ∈ s, (p : ℝ)⁻¹ ^ 2).trans
    (hprod s hs)

private lemma prime_power_factor_ge (p a : ℕ) (hp : 2 ≤ p) (ha : 0 < a) :
    1 - (p : ℝ)⁻¹ ^ 2 ≤
      ((p : ℝ) ^ (a - 1) * (p - 1)) * (∑ k ∈ range (a + 1), (p : ℝ) ^ k) /
        ((p : ℝ) ^ a) ^ 2 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hsum : (p : ℝ) ^ (b + 1) + (p : ℝ) ^ b ≤
      ∑ k ∈ range (b + 1 + 1), (p : ℝ) ^ k := by
    rw [sum_range_succ]
    have h := single_le_sum (fun k _ ↦ pow_nonneg hp0.le k)
      (mem_range.mpr (Nat.lt_succ_self b))
    linarith
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  calc
    _ = ((p : ℝ) ^ b * (p - 1)) * ((p : ℝ) ^ (b + 1) + (p : ℝ) ^ b) /
        ((p : ℝ) ^ (b + 1)) ^ 2 := by
      rw [pow_succ]
      field_simp
      ring
    _ ≤ _ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (mul_nonneg (pow_nonneg hp0.le b)
          (by linarith))) (sq_nonneg _)

private lemma totient_mul_sigma_ge (n : ℕ) (hn : 0 < n) :
    (1 / 4 : ℝ) ≤ (Nat.totient n : ℝ) / n * ((ArithmeticFunction.sigma 1 n : ℝ) / n) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hphi : (Nat.totient n : ℝ) =
      ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p - 1) * (p - 1) := by
    rw [Nat.totient_eq_prod_factorization hn0, Nat.prod_factorization_eq_prod_primeFactors,
      Nat.cast_prod]
    refine prod_congr rfl fun p hp ↦ ?_
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by
      linarith [(Nat.prime_of_mem_primeFactors hp).two_le])]
    norm_num
  have hsigma : (ArithmeticFunction.sigma 1 n : ℝ) =
      ∏ p ∈ n.primeFactors, ∑ k ∈ range (n.factorization p + 1), (p : ℝ) ^ k := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
    simp only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, mul_one]
  have hnorm : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn0
  have hprod := prod_one_sub_inv_sq_ge n.primeFactors
    (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le)
  calc
    _ ≤ ∏ p ∈ n.primeFactors,
        ((p : ℝ) ^ (n.factorization p - 1) * (p - 1)) *
          (∑ k ∈ range (n.factorization p + 1), (p : ℝ) ^ k) /
            ((p : ℝ) ^ n.factorization p) ^ 2 := by
      apply hprod.trans
      refine Finset.prod_le_prod₀ (fun p hp ↦ ?_) (fun p hp ↦ ?_)
      · have hp2 : (2 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hi := inv_le_one_of_one_le₀ (show (1 : ℝ) ≤ p by linarith)
        have hi0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
        nlinarith
      · apply prime_power_factor_ge p (n.factorization p)
          (Nat.prime_of_mem_primeFactors hp).two_le
        exact (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn0
          (Nat.dvd_of_mem_primeFactors hp)
    _ = _ := by
      rw [prod_div_distrib, prod_mul_distrib, prod_pow, ← hphi, ← hsigma, ← hnorm]
      ring

private lemma log_log_pos (n : ℕ) (hn : 3 ≤ n) : 0 < Real.log (Real.log n) := by
  apply Real.log_pos
  apply (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < n)).mpr
  have h := Real.exp_one_lt_three
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private lemma sigma_uniform_bound : ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 3 ≤ n →
    (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ D * Real.log (Real.log n) := by
  classical
  let F (n : ℕ) := (ArithmeticFunction.sigma 1 n : ℝ) /
    ((n : ℝ) * Real.log (Real.log n))
  let G := Real.exp Real.eulerMascheroniConstant + 1
  have hG : 0 < G := by dsimp [G]; positivity
  have hlim : limsup F atTop = Real.exp Real.eulerMascheroniConstant :=
    MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted.gronwall_sigma_limsup
  have hbd : ∃ B : ℝ, ∀ᶠ n in atTop, F n ≤ B := by
    by_contra! h
    have he : {B : ℝ | ∀ᶠ n in atTop, F n ≤ B} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun B hB ↦ h B (hB.mono fun _ hle ↦ not_lt_of_ge hle)
    rw [limsup, limsSup] at hlim
    simp only [eventually_map] at hlim
    rw [he, Real.sInf_empty] at hlim
    exact (Real.exp_ne_zero _ hlim.symm).elim
  have he := eventually_lt_of_limsup_lt (show limsup F atTop < G by
    rw [hlim]; dsimp [G]; linarith)
    (let ⟨_, h⟩ := hbd; isBoundedUnder_of_eventually_le h)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  let D := G + ∑ k ∈ range N, |F k|
  have hsum : 0 ≤ ∑ k ∈ range N, |F k| := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, fun n hn ↦ ?_⟩
  have hFn : F n ≤ D := by
    by_cases h : N ≤ n
    · exact (hN n h).le.trans (by dsimp [D]; linarith)
    · have hle := single_le_sum (fun k _ ↦ abs_nonneg (F k))
        (mem_range.mpr (lt_of_not_ge h))
      exact (le_abs_self (F n)).trans (hle.trans (by dsimp [D]; linarith))
  have hl := log_log_pos n hn
  dsimp [F] at hFn
  rw [div_mul_eq_div_div] at hFn
  exact (div_le_iff₀ hl).mp hFn

/-- **Lower bound for Euler's function and upper bound for the sum of divisors.** Let $\varphi$
be Euler's totient function and $\sigma(n)$ the sum of the positive divisors of $n$. There is a
constant $C > 0$ such that $\varphi(n)/n \ge C/\log\log n$ for every integer $n \ge 3$, and there
is a constant $C'$ such that $\sigma(n)/n \le C' \log\log n$ for every integer $n \ge 3$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 1 (`fq-2024-luca09162024rev2-lem-1`),
quoted from Hardy and Wright, Theorems 323, 328 and 329. -/
public theorem totient_div_gg_and_sigma_div_ll_log_log :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
        C / Real.log (Real.log n) ≤ (Nat.totient n : ℝ) / n) ∧
      ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
        (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ C * Real.log (Real.log n)
    := by
  obtain ⟨D, hD, hσ⟩ := sigma_uniform_bound
  refine ⟨⟨1 / (4 * D), by positivity, fun n hn ↦ ?_⟩, ⟨D, hσ⟩⟩
  have hn0 : 0 < n := by omega
  have hφ : 0 ≤ (Nat.totient n : ℝ) / n := by positivity
  have hl := log_log_pos n hn
  have hbridge := totient_mul_sigma_ge n hn0
  have hbound := mul_le_mul_of_nonneg_left (hσ n hn) hφ
  have hquarter : (1 / 4 : ℝ) ≤ (Nat.totient n : ℝ) / n *
      (D * Real.log (Real.log n)) := by
    exact hbridge.trans hbound
  apply (div_le_iff₀ hl).mpr
  apply (div_le_iff₀ (show 0 < 4 * D by positivity)).mpr
  nlinarith

end

open Finset Real

private noncomputable def weight (s : ℝ) (hs : 1 < s) : ℕ →* ℝ where
  toFun n := (5 / 3 : ℝ) ^ ArithmeticFunction.cardFactors n * (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · subst m
      simp [zero_rpow (by linarith : -s ≠ 0)]
    by_cases hn : n = 0
    · subst n
      simp [zero_rpow (by linarith : -s ≠ 0)]
    rw [ArithmeticFunction.cardFactors_mul hm hn, pow_add, Nat.cast_mul,
      mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

private noncomputable def reciprocalPower (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by simp [mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

private theorem reciprocalPower_sum_le (s : ℝ) (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ 1 + 1 / (s - 1) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : (∑' n : ℕ, (n : ℝ) ^ (-s)) =
      ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s := by
    rw [hsum.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_rpow (by linarith : -s ≠ 0), zero_add]
    apply tsum_congr
    intro n
    rw [Nat.cast_add, Nat.cast_one, rpow_neg (by positivity), one_div]
  rw [hshift]
  have h := ZetaAsymptotics.zeta_limit_aux1 hs
  have hnonneg : 0 ≤ ZetaAsymptotics.termTSum s :=
    tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) s)
  nlinarith

private theorem prime_reciprocal_le (s : ℝ) (hs : 1 < s) (p : ℕ) (hp : p.Prime) :
    (p : ℝ) ^ (-s) ≤ (p : ℝ)⁻¹ := by
  calc
    _ ≤ (p : ℝ) ^ (-1 : ℝ) :=
      rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (by linarith)
    _ = _ := rpow_neg_one _

private theorem weight_prime_lt (s : ℝ) (hs : 1 < s) (p : ℕ) (hp : p.Prime) :
    ‖weight s hs p‖ < 1 := by
  have h := prime_reciprocal_le s hs p hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ht : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div, inv_le_inv₀ (by positivity) (by positivity)]
    exact hp'
  simp only [weight, MonoidHom.coe_mk, OneHom.coe_mk,
    ArithmeticFunction.cardFactors_apply_prime hp, pow_one]
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith

private theorem local_factor_le (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 / 3) :
    (1 - (5 / 3) * t)⁻¹ ≤ ((1 - t)⁻¹) ^ 2 := by
  have h1 : 0 < 1 - t := by linarith
  have h2 : 0 < 1 - (5 / 3) * t := by linarith
  rw [inv_pow, inv_le_inv₀ h2 (sq_pos_of_pos h1)]
  nlinarith [mul_nonneg ht (sub_nonneg.mpr ht')]

private theorem reciprocal_prime_lt (s : ℝ) (hs : 1 < s) (p : ℕ) (hp : p.Prime) :
    ‖reciprocalPower s p‖ < 1 := by
  rw [Real.norm_of_nonneg (by
    change 0 ≤ (p : ℝ) ^ (-s)
    positivity : 0 ≤ reciprocalPower s p)]
  have h := prime_reciprocal_le s hs p hp
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp'
  exact h.trans_lt hi

private theorem euler_factor_bound (s : ℝ) (hs : 1 < s) (N : ℕ) :
    (∏ p ∈ N.primesBelow, (1 - weight s hs p)⁻¹) ≤
      6 * (∏ p ∈ N.primesBelow, (1 - reciprocalPower s p)⁻¹) ^ 2 := by
  let P := N.primesBelow.erase 2
  have hpos (p : ℕ) (hp : p ∈ N.primesBelow) : 0 < 1 - weight s hs p := by
    have h := weight_prime_lt s hs p (Nat.prime_of_mem_primesBelow hp)
    exact sub_pos.mpr ((le_abs_self _).trans_lt h)
  have hcomp (p : ℕ) (hp : p ∈ P) :
      (1 - weight s hs p)⁻¹ ≤ ((1 - reciprocalPower s p)⁻¹) ^ 2 := by
    obtain ⟨hne, hp⟩ := mem_erase.mp hp
    have hprime := Nat.prime_of_mem_primesBelow hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hprime.two_le; omega)
    have ht : reciprocalPower s p ≤ 1 / 3 := by
      apply (prime_reciprocal_le s hs p hprime).trans
      rw [one_div, inv_le_inv₀ (by positivity) (by positivity)]
      exact hp3
    simpa only [weight, reciprocalPower, MonoidHom.coe_mk, OneHom.coe_mk,
      ArithmeticFunction.cardFactors_apply_prime hprime, pow_one] using
      local_factor_le (reciprocalPower s p) (by
        change 0 ≤ (p : ℝ) ^ (-s)
        positivity) ht
  have hP : (∏ p ∈ P, (1 - weight s hs p)⁻¹) ≤
      (∏ p ∈ P, (1 - reciprocalPower s p)⁻¹) ^ 2 := by
    rw [← prod_pow]
    exact prod_le_prod₀ (fun p hp => le_of_lt (inv_pos.mpr (hpos p (mem_of_mem_erase hp)))) hcomp
  have hnonneg : 0 ≤ ∏ p ∈ P, (1 - reciprocalPower s p)⁻¹ :=
    prod_nonneg (fun p hp => by
      have h := reciprocal_prime_lt s hs p (Nat.prime_of_mem_primesBelow (mem_of_mem_erase hp))
      exact inv_nonneg.mpr (sub_nonneg.mpr ((le_abs_self _).trans h.le)))
  by_cases h2 : 2 ∈ N.primesBelow
  · rw [← mul_prod_erase _ _ h2, ← mul_prod_erase _ _ h2]
    have htwo : (1 - weight s hs 2)⁻¹ ≤ 6 := by
      have h := prime_reciprocal_le s hs 2 Nat.prime_two
      have ha : 0 < 1 - weight s hs 2 := hpos 2 h2
      have hden : (1 / 6 : ℝ) ≤ 1 - weight s hs 2 := by
        simp only [weight, MonoidHom.coe_mk, OneHom.coe_mk,
          ArithmeticFunction.cardFactors_apply_prime Nat.prime_two, pow_one]
        norm_num at h
        linarith
      have hi := (inv_le_inv₀ ha (by norm_num : (0 : ℝ) < 1 / 6)).mpr hden
      norm_num at hi
      exact hi
    have htwo' : 1 ≤ (1 - reciprocalPower s 2)⁻¹ := by
      have h := reciprocal_prime_lt s hs 2 Nat.prime_two
      have hn : 0 ≤ reciprocalPower s 2 := by
        change 0 ≤ (2 : ℝ) ^ (-s)
        positivity
      have hi := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1)
        (sub_pos.mpr ((le_abs_self _).trans_lt h))).mpr (by linarith : 1 - reciprocalPower s 2 ≤ 1)
      simpa using hi
    calc
      _ ≤ 6 * (∏ p ∈ P, (1 - reciprocalPower s p)⁻¹) ^ 2 :=
        mul_le_mul htwo hP
          (prod_nonneg (fun p hp => (inv_pos.mpr (hpos p (mem_of_mem_erase hp))).le))
          (by norm_num)
      _ ≤ _ := by gcongr; exact le_mul_of_one_le_left hnonneg htwo'
  · have he : P = N.primesBelow := erase_eq_of_notMem h2
    rw [← he]
    exact hP.trans (le_mul_of_one_le_left (sq_nonneg _) (by norm_num))

private theorem sum_le_euler (f : ℕ →* ℝ) (hf : ∀ n, 0 ≤ f n)
    (hp : ∀ p : ℕ, p.Prime → ‖f p‖ < 1) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n) ≤ ∏ p ∈ (N + 1).primesBelow, (1 - f p)⁻¹ := by
  obtain ⟨hsum, heuler⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (fun {p} h => hp p h) (N + 1)
  have hmem (n : ℕ) (hn : n ∈ Icc 1 N) : n ∈ (N + 1).smoothNumbers :=
    Nat.mem_smoothNumbers_of_lt (mem_Icc.mp hn).1 (by have := (mem_Icc.mp hn).2; omega)
  rw [← heuler.tsum_eq, ← sum_subtype_of_mem (f := fun n => f n) hmem]
  exact hsum.of_norm.sum_le_tsum _ (fun n _ => hf n)

private theorem weighted_sum_bound (s : ℝ) (hs : 1 < s) (N : ℕ) :
    (∑ n ∈ Icc 1 N, weight s hs n) ≤ 6 * (1 + 1 / (s - 1)) ^ 2 := by
  have hsum : Summable (fun n : ℕ => reciprocalPower s n) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hz : (∏ p ∈ (N + 1).primesBelow, (1 - reciprocalPower s p)⁻¹) ≤
      1 + 1 / (s - 1) := by
    obtain ⟨_, heuler⟩ :=
      EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
        (f := reciprocalPower s) (fun {p} h => reciprocal_prime_lt s hs p h) (N + 1)
    rw [← heuler.tsum_eq]
    exact (hsum.tsum_subtype_le _ _ (fun n => rpow_nonneg (Nat.cast_nonneg n) _)).trans
      (reciprocalPower_sum_le s hs)
  calc
    _ ≤ ∏ p ∈ (N + 1).primesBelow, (1 - weight s hs p)⁻¹ :=
      sum_le_euler (weight s hs) (fun n => by
        change 0 ≤ (5 / 3 : ℝ) ^ ArithmeticFunction.cardFactors n * (n : ℝ) ^ (-s)
        positivity) (weight_prime_lt s hs) N
    _ ≤ 6 * (∏ p ∈ (N + 1).primesBelow, (1 - reciprocalPower s p)⁻¹) ^ 2 :=
      euler_factor_bound s hs (N + 1)
    _ ≤ _ := by
      gcongr
      · exact prod_nonneg (fun p hp => by
          have h := reciprocal_prime_lt s hs p (Nat.prime_of_mem_primesBelow hp)
          exact inv_nonneg.mpr (sub_nonneg.mpr ((le_abs_self _).trans h.le)))

private theorem log_ge_one (x : ℝ) (hx : 10 ≤ x) : 1 ≤ log x := by
  have he : exp 1 < x := exp_one_lt_d9.trans_le (by linarith)
  exact (lt_log_iff_exp_lt (by linarith : 0 < x)).mpr he |>.le

private theorem weight_sum_le (x : ℝ) (hx : 10 ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, (5 / 3 : ℝ) ^ ArithmeticFunction.cardFactors n) ≤
      24 * exp 1 * x * log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ log x := log_ge_one x hx
  have hl0 : 0 < log x := by linarith
  let s : ℝ := 1 + 1 / log x
  have hs : 1 < s := by dsimp [s]; linarith [one_div_pos.mpr hl0]
  have hterm (n : ℕ) (hn : n ∈ Icc 1 ⌊x⌋₊) :
      (5 / 3 : ℝ) ^ ArithmeticFunction.cardFactors n ≤ x ^ s * weight s hs n := by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
    have hnle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp (mem_Icc.mp hn).2
    have hw : 0 ≤ weight s hs n := by
      change 0 ≤ (5 / 3 : ℝ) ^ ArithmeticFunction.cardFactors n * (n : ℝ) ^ (-s)
      positivity
    calc
      _ = (n : ℝ) ^ s * weight s hs n := by
        simp only [weight, MonoidHom.coe_mk, OneHom.coe_mk, rpow_neg hn0.le]
        rw [mul_left_comm, mul_inv_cancel₀ (rpow_pos_of_pos hn0 s).ne', mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right (rpow_le_rpow hn0.le hnle (by linarith)) hw
  have hxs : x ^ s = exp 1 * x := by
    rw [rpow_def_of_pos hx0]
    have h : log x * s = 1 + log x := by dsimp [s]; field_simp; ring
    rw [h, exp_add, exp_log hx0]
  have hs' : 1 + 1 / (s - 1) = 1 + log x := by
    dsimp [s]
    simp
  calc
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, x ^ s * weight s hs n := sum_le_sum hterm
    _ = x ^ s * ∑ n ∈ Icc 1 ⌊x⌋₊, weight s hs n := (mul_sum ..).symm
    _ ≤ x ^ s * (6 * (1 + 1 / (s - 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left (weighted_sum_bound s hs _) (rpow_nonneg hx0.le s)
    _ = 6 * exp 1 * x * (1 + log x) ^ 2 := by rw [hxs, hs']; ring
    _ ≤ 6 * exp 1 * x * (2 * log x) ^ 2 := by gcongr; linarith
    _ = _ := by ring

private theorem threshold_weight_le (x : ℝ) (hx : 10 ≤ x) (n : ℕ)
    (hn : 10 * log (log x) ≤ (ArithmeticFunction.cardFactors n : ℝ)) :
    log x ^ 4 ≤ (5 / 3 : ℝ) ^ ArithmeticFunction.cardFactors n := by
  have hl : 1 ≤ log x := log_ge_one x hx
  have hl0 : 0 < log x := by linarith
  have hll : 0 ≤ log (log x) := log_nonneg hl
  have hr : (2 / 5 : ℝ) ≤ log (5 / 3 : ℝ) := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5 / 3)
    norm_num at h
    exact h
  rw [← rpow_natCast (log x) 4, ← rpow_natCast (5 / 3 : ℝ) (ArithmeticFunction.cardFactors n),
    rpow_def_of_pos hl0, rpow_def_of_pos (by norm_num : (0 : ℝ) < 5 / 3)]
  apply exp_le_exp.mpr
  norm_num
  have hΩ : 0 ≤ (ArithmeticFunction.cardFactors n : ℝ) := by positivity
  nlinarith [mul_nonneg hΩ (sub_nonneg.mpr hr)]

/-- **Integers with many prime factors are rare.** Let $\Omega(n)$ be the number of prime factors
of $n$ counted with multiplicity. There is a constant $C$ such that for every real $x \ge 10$, the
number of integers $1 \le n \le x$ with $\Omega(n) \ge 10 \log\log x$ is at most
$C x / (\log x)^2$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 3 (`fq-2024-luca09162024rev2-lem-3`). -/
public theorem card_cardFactors_ge_ten_log_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 10 ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          10 * Real.log (Real.log x) ≤ (ArithmeticFunction.cardFactors n : ℝ))).card ≤
        C * x / Real.log x ^ 2 := by
  classical
  refine ⟨24 * exp 1, fun x hx => ?_⟩
  have hl0 : 0 < log x := by have := log_ge_one x hx; linarith
  let S := (Icc 1 ⌊x⌋₊).filter (fun n =>
    10 * log (log x) ≤ (ArithmeticFunction.cardFactors n : ℝ))
  have hbound : (S.card : ℝ) * log x ^ 4 ≤ 24 * exp 1 * x * log x ^ 2 := calc
    _ = ∑ _n ∈ S, log x ^ 4 := by simp
    _ ≤ ∑ n ∈ S, (5 / 3 : ℝ) ^ ArithmeticFunction.cardFactors n :=
      sum_le_sum (fun n hn => threshold_weight_le x hx n (mem_filter.mp hn).2)
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, (5 / 3 : ℝ) ^ ArithmeticFunction.cardFactors n :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => by positivity)
    _ ≤ _ := weight_sum_le x hx
  apply (le_div_iff₀ (sq_pos_of_pos hl0)).mpr
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hl0)).mp
  convert hbound using 1 <;> ring

end MetaMathlibExt
