/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Defs
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Rat.Cast.Order
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryFortyOne
import MathlibExt.NumberTheory.ArithmeticFunction.UnitaryConvolution
import MathlibExt.NumberTheory.BangZsigmondy
import MathlibExt.NumberTheory.PrimitivePrimeDivisorPowAddOne
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Biunitary triperfect numbers with prescribed exponents

A biunitary triperfect number with exponent four at two and exponent at least five at three
is not divisible by five.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 15.
-/

namespace MetaMathlibExt

private theorem gcdUnitary_eq_one_iff (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    gcdUnitary a b = 1 ↔ ∀ u, u ∈ a.unitaryDivisors → u ∈ b.unitaryDivisors → u = 1 := by
  constructor
  · intro h u hua hub
    have hu := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_unitaryDivisors hua) (Nat.pos_of_ne_zero ha)
    have := le_gcdUnitary hua hub
    omega
  · intro h
    exact h _ (gcdUnitary_mem_unitaryDivisors ha hb).1
      (gcdUnitary_mem_unitaryDivisors ha hb).2

private theorem gcd_projection_eq (a b c d u : ℕ) (had : a.Coprime d) (hcb : c.Coprime b)
    (huab : u ∣ a * b) (hucd : u ∣ c * d) : u.gcd a = u.gcd c := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left u a)
    exact ((had.coprime_dvd_left (Nat.gcd_dvd_right u a)).dvd_mul_right).mp
      ((Nat.gcd_dvd_left u a).trans hucd)
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left u c)
    exact ((hcb.coprime_dvd_left (Nat.gcd_dvd_right u c)).dvd_mul_right).mp
      ((Nat.gcd_dvd_left u c).trans huab)

private theorem gcdUnitary_mul_eq_one_iff (a b c d : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a.Coprime b) (had : a.Coprime d) (hcb : c.Coprime b) (hcd : c.Coprime d) :
    gcdUnitary (a * b) (c * d) = 1 ↔ gcdUnitary a c = 1 ∧ gcdUnitary b d = 1 := by
  rw [gcdUnitary_eq_one_iff _ _ (mul_ne_zero ha hb) (mul_ne_zero hc hd),
    gcdUnitary_eq_one_iff _ _ ha hc, gcdUnitary_eq_one_iff _ _ hb hd]
  constructor
  · intro h
    constructor
    · intro u hua huc
      apply h u
      · simpa using Nat.mul_mem_unitaryDivisors_mul hab hua
          (show 1 ∈ b.unitaryDivisors by simp [hb])
      · simpa using Nat.mul_mem_unitaryDivisors_mul hcd huc
          (show 1 ∈ d.unitaryDivisors by simp [hd])
    · intro u hub hud
      apply h u
      · simpa using Nat.mul_mem_unitaryDivisors_mul hab
          (show 1 ∈ a.unitaryDivisors by simp [ha]) hub
      · simpa using Nat.mul_mem_unitaryDivisors_mul hcd
          (show 1 ∈ c.unitaryDivisors by simp [hc]) hud
  · rintro ⟨hac, hbd⟩ u huab hucd
    have huab' := Nat.dvd_of_mem_unitaryDivisors huab
    have hucd' := Nat.dvd_of_mem_unitaryDivisors hucd
    have heq := gcd_projection_eq a b c d u had hcb huab' hucd'
    have heq' := gcd_projection_eq b a d c u hcb.symm had.symm
      (by simpa [mul_comm] using huab') (by simpa [mul_comm] using hucd')
    have h1 : u.gcd a = 1 := hac _
      (Nat.gcd_mem_unitaryDivisors_of_mem_mul hab huab)
      (heq ▸ Nat.gcd_mem_unitaryDivisors_of_mem_mul hcd hucd)
    have h2 : u.gcd b = 1 := hbd _
      (Nat.gcd_mem_unitaryDivisors_of_mem_mul hab.symm (by simpa [mul_comm] using huab))
      (heq' ▸ Nat.gcd_mem_unitaryDivisors_of_mem_mul hcd.symm
        (by simpa [mul_comm] using hucd))
    have hsplit := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hab).mpr huab'
    simpa [h1, h2] using hsplit.symm

private theorem mul_mem_biunitary_iff (m n a b : ℕ) (hmn : m.Coprime n)
    (ha : a ∣ m) (hb : b ∣ n) (hm : m ≠ 0) (hn : n ≠ 0) :
    a * b ∈ biunitaryDivisors (m * n) ↔
      a ∈ biunitaryDivisors m ∧ b ∈ biunitaryDivisors n := by
  have ha0 := ne_zero_of_dvd_ne_zero hm ha
  have hb0 := ne_zero_of_dvd_ne_zero hn hb
  have hc0 := ne_zero_of_dvd_ne_zero hm (Nat.div_dvd_of_dvd ha)
  have hd0 := ne_zero_of_dvd_ne_zero hn (Nat.div_dvd_of_dvd hb)
  simp only [mem_biunitaryDivisors, ha, hb, Nat.mul_dvd_mul ha hb, ne_eq, hm, hn,
    mul_ne_zero hm hn, not_false_eq_true, true_and, ← Nat.div_mul_div_comm ha hb]
  exact gcdUnitary_mul_eq_one_iff a b (m / a) (n / b) ha0 hb0 hc0 hd0
    ((hmn.coprime_dvd_left ha).coprime_dvd_right hb)
    ((hmn.coprime_dvd_left ha).coprime_dvd_right (Nat.div_dvd_of_dvd hb))
    ((hmn.coprime_dvd_left (Nat.div_dvd_of_dvd ha)).coprime_dvd_right hb)
    ((hmn.coprime_dvd_left (Nat.div_dvd_of_dvd ha)).coprime_dvd_right
      (Nat.div_dvd_of_dvd hb))

private theorem sigmaBiunitary_mul (m n : ℕ) (hmn : m.Coprime n) :
    sigmaBiunitary (m * n) = sigmaBiunitary m * sigmaBiunitary n := by
  classical
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [sigmaBiunitary]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun x => x.1 * x.2) (fun d => (d.gcd m, d.gcd n)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact (mul_mem_biunitary_iff m n a b hmn
      (dvd_of_mem_biunitaryDivisors ha) (dvd_of_mem_biunitaryDivisors hb) hm hn).mpr ⟨ha, hb⟩
  · intro d hd
    have hdvd := dvd_of_mem_biunitaryDivisors hd
    have hs := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hmn).mpr hdvd
    exact Finset.mem_product.mpr ((mul_mem_biunitary_iff m n _ _ hmn
      (Nat.gcd_dvd_right d m) (Nat.gcd_dvd_right d n) hm hn).mp (by rw [hs]; exact hd))
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have ham := dvd_of_mem_biunitaryDivisors ha
    have hbn := dvd_of_mem_biunitaryDivisors hb
    simp only [Prod.mk.injEq]
    exact ⟨by rw [Nat.Coprime.gcd_mul_right_cancel a (hmn.symm.coprime_dvd_left hbn),
      Nat.gcd_eq_left ham], by rw [Nat.Coprime.gcd_mul_left_cancel b
      (hmn.coprime_dvd_left ham), Nat.gcd_eq_left hbn]⟩
  · intro d hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hmn).mpr
      (dvd_of_mem_biunitaryDivisors hd)
  · rintro ⟨a, b⟩ _
    rfl

private theorem sigmaBiunitary_ge (n : ℕ) : n ≤ sigmaBiunitary n := by
  by_cases hn : n = 0
  · simp [hn]
  have hmem : n ∈ biunitaryDivisors n := by
    refine mem_biunitaryDivisors.mpr ⟨dvd_rfl, hn, ?_⟩
    rw [Nat.div_self (Nat.pos_of_ne_zero hn), gcdUnitary_eq_one_iff n 1 hn (by decide)]
    intro u _ hu
    exact Nat.dvd_one.mp (Nat.dvd_of_mem_unitaryDivisors hu)
  exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hmem

private theorem sigmaBiunitary_prod (n : ℕ) (hn : n ≠ 0) :
    sigmaBiunitary n = ∏ p ∈ n.primeFactors, sigmaBiunitary (p ^ n.factorization p) := by
  have h := Nat.multiplicative_factorization sigmaBiunitary
    (fun m k hmk => sigmaBiunitary_mul m k hmk) sigmaBiunitary_one hn
  simpa only [Finsupp.prod, Nat.support_factorization] using h

private theorem sigmaBiunitary_prod_dvd (n : ℕ) (hn : n ≠ 0) (s : Finset ℕ)
    (hs : s ⊆ n.primeFactors) :
    (∏ p ∈ s, sigmaBiunitary (p ^ n.factorization p)) ∣ sigmaBiunitary n := by
  rw [sigmaBiunitary_prod n hn]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hs

private theorem sigmaBiunitary_ratio_prod (n : ℕ) (hn : n ≠ 0) :
    (sigmaBiunitary n : ℚ) / n =
      ∏ p ∈ n.primeFactors, (sigmaBiunitary (p ^ n.factorization p) : ℚ) /
        (p : ℚ) ^ n.factorization p := by
  rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← sigmaBiunitary_prod n hn]
  congr 1
  simpa only [Nat.cast_prod, Nat.cast_pow] using congrArg (fun x : ℕ => (x : ℚ))
    (Nat.prod_primeFactors_pow_factorization hn)

private theorem sigmaBiunitary_ratio_ge_one (n : ℕ) (hn : n ≠ 0) :
    (1 : ℚ) ≤ (sigmaBiunitary n : ℚ) / n := by
  apply (le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
  simpa only [one_mul] using (show (n : ℚ) ≤ sigmaBiunitary n by
    exact_mod_cast sigmaBiunitary_ge n)

private theorem sigmaBiunitary_ratio_bound (n : ℕ) (hn : n ≠ 0) (s : Finset ℕ)
    (hs : s ⊆ n.primeFactors) (b : ℕ → ℚ) (hb : ∀ p ∈ s, 0 ≤ b p)
    (hbound : ∀ p ∈ s, b p ≤ (sigmaBiunitary (p ^ n.factorization p) : ℚ) /
      (p : ℚ) ^ n.factorization p) :
    (∏ p ∈ s, b p) ≤ (sigmaBiunitary n : ℚ) / n := by
  rw [sigmaBiunitary_ratio_prod n hn]
  apply le_trans (Finset.prod_le_prod₀ hb hbound)
  apply Finset.prod_le_prod_of_subset_of_one_le₀ hs (fun _ _ => by positivity)
  intro p hp _
  simpa only [Nat.cast_pow] using sigmaBiunitary_ratio_ge_one
    (p ^ n.factorization p) (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)

private theorem not_thirtyTwo_dvd_sigmaBiunitary (n : ℕ) (hn : n ≠ 0)
    (hσ : sigmaBiunitary n = 3 * n) (he : n.factorization 2 = 4) :
    ¬ 32 ∣ sigmaBiunitary n := by
  intro h
  rw [hσ] at h
  have hd : 2 ^ 5 ∣ n := (show Nat.Coprime 32 3 by decide).dvd_mul_left.mp h
  have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hn).mp hd
  omega

private theorem prime_mem (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) (hd : p ∣ n) :
    p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩

private theorem sigma_prime_power_dvd (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) (hd : p ∣ n) :
    sigmaBiunitary (p ^ n.factorization p) ∣ sigmaBiunitary n := by
  simpa using sigmaBiunitary_prod_dvd n hn {p}
    (Finset.singleton_subset_iff.mpr (prime_mem n p hn hp hd))

private theorem force_prime (n p q : ℕ) (hn : n ≠ 0) (hσ : sigmaBiunitary n = 3 * n)
    (hp : p.Prime) (hpn : p ∣ n) (hq : q.Prime) (hq3 : q ≠ 3)
    (hd : q ∣ sigmaBiunitary (p ^ n.factorization p)) : q ∣ n := by
  have h := hd.trans (sigma_prime_power_dvd n p hn hp hpn)
  rw [hσ] at h
  exact (hq.dvd_mul.mp h).resolve_left
    (fun hqdiv => hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hqdiv))

private theorem prime_power_sum (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    sigmaBiunitary (p ^ e) = ∑ i ∈ Finset.range (e + 1),
      if 2 * i = e then 0 else p ^ i := by
  have hmem (i : ℕ) (hi : i ≤ e) :
      gcdUnitary (p ^ i) (p ^ e / p ^ i) = 1 ↔ 2 * i ≠ e := by
    rw [Nat.pow_div hi hp.pos]
    constructor
    · intro h hmid
      have heq : e - i = i := by omega
      have hm : p ^ i ∈ (p ^ i).unitaryDivisors := by
        simp [Nat.unitaryDivisors_prime_pow hp]
      rw [heq] at h
      have hle := le_gcdUnitary hm hm
      rw [h] at hle
      exact (Nat.one_lt_pow (by omega : i ≠ 0) hp.one_lt).not_ge hle
    · intro hmid
      obtain ⟨h₁, h₂⟩ := gcdUnitary_mem_unitaryDivisors
        (pow_ne_zero i hp.ne_zero) (pow_ne_zero (e - i) hp.ne_zero)
      simp only [Nat.unitaryDivisors_prime_pow hp, Finset.mem_insert,
        Finset.mem_singleton] at h₁ h₂
      rcases h₁ with h | h
      · exact h
      rcases h₂ with h' | h'
      · exact h'
      have heq := Nat.pow_right_injective hp.two_le (h.symm.trans h')
      omega
  rw [sigmaBiunitary, biunitaryDivisors, Finset.sum_filter, Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  simp [hmem i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), ite_not]

private theorem prime_power_blocks (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    sigmaBiunitary (p ^ e) = (p ^ (e / 2 + 1) + 1) *
      ∑ i ∈ Finset.range ((e + 1) / 2), p ^ i := by
  let n := e / 2 + 1
  let k := (e + 1) / 2
  have hsplit : e + 1 = n + k := by dsimp [n, k]; omega
  have hblocks : n = k ∨ n = k + 1 := by dsimp [n, k]; omega
  let f (i : ℕ) := if 2 * i = e then 0 else p ^ i
  have low : ∑ i ∈ Finset.range k, f i = ∑ i ∈ Finset.range k, p ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    simp [f, show 2 * i ≠ e by omega]
  have lowBlock : ∑ i ∈ Finset.range n, f i = ∑ i ∈ Finset.range k, p ^ i := by
    rcases hblocks with h | h
    · rwa [h]
    · rw [h, Finset.sum_range_succ, low]
      simp [f, show 2 * k = e by omega]
  rw [prime_power_sum p e hp he]
  change (∑ i ∈ Finset.range (e + 1), f i) =
    (p ^ n + 1) * (∑ i ∈ Finset.range k, p ^ i)
  rw [hsplit, Finset.sum_range_add, lowBlock, add_mul, one_mul, add_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [f, show 2 * (n + i) ≠ e by omega, pow_add]

private theorem prime_power_two (p : ℕ) (hp : p.Prime) :
    sigmaBiunitary (p ^ 2) = 1 + p ^ 2 := by
  rw [prime_power_sum p 2 hp (by decide)]
  simp [Finset.sum_range_succ]

private theorem sigma_three_six : sigmaBiunitary (3 ^ 6) = 1066 := by
  rw [prime_power_sum 3 6 Nat.prime_three (by decide)]
  norm_num [Finset.sum_range_succ]

private theorem three_ratio_gt (e : ℕ) (he : 5 ≤ e) (he6 : e ≠ 6) :
    (40 / 27 : ℚ) < (sigmaBiunitary (3 ^ e) : ℚ) / (3 : ℚ) ^ e := by
  let w (i : ℕ) : ℚ := if 2 * (e - i) = e then 0 else 1 / (3 : ℚ) ^ i
  have hnormalized : (sigmaBiunitary (3 ^ e) : ℚ) / (3 : ℚ) ^ e =
      ∑ i ∈ Finset.range (e + 1), w i := by
    rw [prime_power_sum 3 e Nat.prime_three (by omega), Nat.cast_sum, Finset.sum_div,
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hie : i ≤ e := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simp only [Nat.add_sub_cancel, Nat.cast_ite, Nat.cast_zero, Nat.cast_pow, w]
    split
    · simp
    · norm_num only [Nat.cast_ofNat]
      apply (div_eq_div_iff (by positivity) (by positivity)).2
      rw [← pow_add, Nat.sub_add_cancel hie, one_mul]
  have hpartial : (∑ i ∈ ({0, 1, 2, 3, e} : Finset ℕ), 1 / (3 : ℚ) ^ i) ≤
      (sigmaBiunitary (3 ^ e) : ℚ) / (3 : ℚ) ^ e := by
    rw [hnormalized]
    calc
      _ = ∑ i ∈ ({0, 1, 2, 3, e} : Finset ℕ), w i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        have hmid : 2 * (e - i) ≠ e := by
          rcases hi with rfl | rfl | rfl | rfl | rfl <;> omega
        simp [w, hmid]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (by intro i hi; simp only [Finset.mem_range];
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega)
        (fun i _ _ => by dsimp [w]; split <;> positivity)
  norm_num [Finset.sum_insert, show 0 ≠ e by omega, show 1 ≠ e by omega,
    show 2 ≠ e by omega, show 3 ≠ e by omega] at hpartial
  have : (0 : ℚ) < ((3 : ℚ) ^ e)⁻¹ := by positivity
  linarith

private theorem partial_ratio_le_three (n : ℕ) (hn : n ≠ 0)
    (hσ : sigmaBiunitary n = 3 * n) (s : Finset ℕ) (hs : s ⊆ n.primeFactors)
    (b : ℕ → ℚ) (hb : ∀ p ∈ s, 0 ≤ b p)
    (hbound : ∀ p ∈ s, b p ≤ (sigmaBiunitary (p ^ n.factorization p) : ℚ) /
      (p : ℚ) ^ n.factorization p) : (∏ p ∈ s, b p) ≤ 3 := by
  have h := sigmaBiunitary_ratio_bound n hn s hs b hb hbound
  simpa [hσ, hn] using h

private theorem subset_primes (n : ℕ) (hn : n ≠ 0) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ∣ n) : s ⊆ n.primeFactors := by
  intro p hp
  exact prime_mem n p hn (hs p hp).1 (hs p hp).2

private theorem five_exponent_eq_two (n : ℕ) (hn : n ≠ 0)
    (hσ : sigmaBiunitary n = 3 * n) (he : n.factorization 2 = 4)
    (hf : 5 ≤ n.factorization 3) (h5 : 5 ∣ n) : n.factorization 5 = 2 := by
  have h2 : 2 ∣ n := (Nat.prime_two.dvd_iff_one_le_factorization hn).mpr (by omega)
  have h3 : 3 ∣ n := (Nat.prime_three.dvd_iff_one_le_factorization hn).mpr (by omega)
  have hg : 0 < n.factorization 5 :=
    (Nat.prime_five.dvd_iff_one_le_factorization hn).mp h5
  by_contra hg2
  have hf6 : n.factorization 3 = 6 := by
    by_contra hf6
    let b (p : ℕ) : ℚ := if p = 2 then 27 / 16 else if p = 3 then
      (sigmaBiunitary (3 ^ n.factorization 3) : ℚ) / (3 : ℚ) ^ n.factorization 3 else 6 / 5
    have hs := subset_primes n hn {2, 3, 5} (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨Nat.prime_two, h2⟩
      · exact ⟨Nat.prime_three, h3⟩
      · exact ⟨Nat.prime_five, h5⟩)
    have ht := partial_ratio_le_three n hn hσ {2, 3, 5} hs b (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> dsimp [b] <;> positivity) (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · norm_num [b, he, sigmaBiunitary_sixteen]
      · simp [b]
      · have h := (sigmaBiunitary_prime_pow_div_ge 5 _ Nat.prime_five hg).2.1 hg2
        norm_num only [Nat.cast_ofNat] at h
        simpa [b] using h)
    norm_num [b, Finset.prod_insert] at ht
    have hgt := three_ratio_gt _ hf hf6
    simp only [Nat.factorization_def n Nat.prime_three] at ht hgt
    linarith
  have h13 : 13 ∣ n := force_prime n 3 13 hn hσ Nat.prime_three h3 (by decide)
    (by decide) (by rw [hf6, sigma_three_six]; decide)
  have hg13 : 0 < n.factorization 13 :=
    (show Nat.Prime 13 by decide).dvd_iff_one_le_factorization hn |>.mp h13
  have hg13eq : n.factorization 13 = 2 := by
    by_contra hg13eq
    let b (p : ℕ) : ℚ := if p = 2 then 27 / 16 else if p = 3 then 1066 / 729 else
      if p = 5 then 6 / 5 else 14 / 13
    have hs := subset_primes n hn {2, 3, 5, 13} (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨Nat.prime_two, h2⟩
      · exact ⟨Nat.prime_three, h3⟩
      · exact ⟨Nat.prime_five, h5⟩
      · exact ⟨by decide, h13⟩)
    have ht := partial_ratio_le_three n hn hσ {2, 3, 5, 13} hs b (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num [b]) (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · norm_num [b, he, sigmaBiunitary_sixteen]
      · rw [hf6, sigma_three_six]
        norm_num [b]
      · have h := (sigmaBiunitary_prime_pow_div_ge 5 _ Nat.prime_five hg).2.1 hg2
        norm_num only [Nat.cast_ofNat] at h
        simpa [b] using h
      · have h := (sigmaBiunitary_prime_pow_div_ge 13 _ (by decide) hg13).2.1 hg13eq
        norm_num only [Nat.cast_ofNat] at h
        simpa [b] using h)
    norm_num [b, Finset.prod_insert] at ht
  have h17 : 17 ∣ n := force_prime n 13 17 hn hσ (by decide) h13 (by decide)
    (by decide) (by rw [hg13eq, prime_power_two 13 (by decide)]; decide)
  have hg17 : 0 < n.factorization 17 :=
    (show Nat.Prime 17 by decide).dvd_iff_one_le_factorization hn |>.mp h17
  have hg17eq : n.factorization 17 = 2 := by
    by_contra hg17eq
    let b (p : ℕ) : ℚ := if p = 2 then 27 / 16 else if p = 3 then 1066 / 729 else
      if p = 5 then 6 / 5 else if p = 13 then 170 / 169 else 18 / 17
    have hs := subset_primes n hn {2, 3, 5, 13, 17} (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact ⟨Nat.prime_two, h2⟩
      · exact ⟨Nat.prime_three, h3⟩
      · exact ⟨Nat.prime_five, h5⟩
      · exact ⟨by decide, h13⟩
      · exact ⟨by decide, h17⟩)
    have ht := partial_ratio_le_three n hn hσ {2, 3, 5, 13, 17} hs b (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num [b]) (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · norm_num [b, he, sigmaBiunitary_sixteen]
      · rw [hf6, sigma_three_six]
        norm_num [b]
      · have h := (sigmaBiunitary_prime_pow_div_ge 5 _ Nat.prime_five hg).2.1 hg2
        norm_num only [Nat.cast_ofNat] at h
        simpa [b] using h
      · rw [hg13eq, prime_power_two 13 (by decide)]
        norm_num [b]
      · have h := (sigmaBiunitary_prime_pow_div_ge 17 _ (by decide) hg17).2.1 hg17eq
        norm_num only [Nat.cast_ofNat] at h
        simpa [b] using h)
    norm_num [b, Finset.prod_insert] at ht
  have h25 : 25 ∣ n := by
    have hs := subset_primes n hn {13, 17} (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact ⟨by decide, h13⟩
      · exact ⟨by decide, h17⟩)
    have hd := sigmaBiunitary_prod_dvd n hn {13, 17} hs
    have hx : 25 ∣ ∏ p ∈ ({13, 17} : Finset ℕ), sigmaBiunitary (p ^ n.factorization p) := by
      rw [Finset.prod_pair (by decide), hg13eq, hg17eq,
        prime_power_two 13 (by decide), prime_power_two 17 (by decide)]
      norm_num
    have h := hx.trans hd
    rw [hσ] at h
    exact (show Nat.Coprime 25 3 by decide).dvd_mul_left.mp h
  have hg3 : 3 ≤ n.factorization 5 := by
    have h := (Nat.prime_five.pow_dvd_iff_le_factorization hn).mp (show 5 ^ 2 ∣ n from h25)
    omega
  let b (p : ℕ) : ℚ := if p = 2 then 27 / 16 else if p = 3 then 1066 / 729 else
    if p = 5 then 756 / 625 else 170 / 169
  have hs := subset_primes n hn {2, 3, 5, 13} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨Nat.prime_two, h2⟩
    · exact ⟨Nat.prime_three, h3⟩
    · exact ⟨Nat.prime_five, h5⟩
    · exact ⟨by decide, h13⟩)
  have ht := partial_ratio_le_three n hn hσ {2, 3, 5, 13} hs b (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [b]) (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · norm_num [b, he, sigmaBiunitary_sixteen]
    · rw [hf6, sigma_three_six]
      norm_num [b]
    · have h := (sigmaBiunitary_prime_pow_div_ge 5 _ Nat.prime_five hg).2.2 hg3
      norm_num only [Nat.cast_ofNat] at h
      simpa [b] using h
    · rw [hg13eq, prime_power_two 13 (by decide)]
      norm_num [b])
  norm_num [b, Finset.prod_insert] at ht

private theorem even_prime_power_sum (p e : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 0 < e) : 2 ∣ sigmaBiunitary (p ^ e) := by
  rw [prime_power_blocks p e hp he]
  exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp
    ((show Odd (p ^ (e / 2 + 1)) from (hp.odd_of_ne_two hp2).pow).add_odd odd_one)) _

private theorem product_dvd_sigma (n : ℕ) (hn : n ≠ 0) (s : Finset ℕ)
    (hs : s ⊆ n.primeFactors) (a : ℕ → ℕ)
    (ha : ∀ p ∈ s, a p ∣ sigmaBiunitary (p ^ n.factorization p)) :
    (∏ p ∈ s, a p) ∣ sigmaBiunitary n :=
  (Finset.prod_dvd_prod_of_dvd _ _ ha).trans (sigmaBiunitary_prod_dvd n hn s hs)

private theorem odd_prime_product_dvd_sigma (n : ℕ) (hn : n ≠ 0) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ∣ n ∧ p ≠ 2) : 2 ^ s.card ∣ sigmaBiunitary n := by
  simpa using product_dvd_sigma n hn s
    (subset_primes n hn s (fun p hp => ⟨(hs p hp).1, (hs p hp).2.1⟩)) (fun _ => 2)
    (fun p hp => even_prime_power_sum p _ (hs p hp).1 (hs p hp).2.2
      ((hs p hp).1.dvd_iff_one_le_factorization hn |>.mp (hs p hp).2.1))

private theorem three_formula (f t η : ℕ) (hη : η ≤ 1) (hft : f + 1 + η = 2 * t)
    (hf : 0 < f) : 2 * sigmaBiunitary (3 ^ f) =
      (3 ^ t + 1) * (3 ^ (t - η) - 1) := by
  have ht : f / 2 + 1 = t := by omega
  have hk : (f + 1) / 2 = t - η := by omega
  rw [prime_power_blocks 3 f Nat.prime_three hf, ht, hk]
  calc
    2 * ((3 ^ t + 1) * ∑ i ∈ Finset.range (t - η), 3 ^ i) =
        (3 ^ t + 1) * ((∑ i ∈ Finset.range (t - η), 3 ^ i) * (3 - 1)) := by ring
    _ = _ := by rw [geom_sum_mul_of_one_le (by decide : 1 ≤ (3 : ℕ))]

private theorem primitive_minus_outside (k : ℕ) (hk : 5 ≤ k) :
    ∃ q, IntegerSequence.IsPrimitivePrimeDivisor (fun m => (3 : ℤ) ^ m - 1) k q ∧
      q ∉ ({2, 3, 5, 13} : Finset ℕ) := by
  obtain ⟨q, hq⟩ := bangZsigmondy_exists_primitivePrimeDivisor (a := 3) (b := 1)
    (n := k) (by decide) (by decide) (by decide) (by omega)
    (by simp only [IsBangZsigmondyExceptional]; omega)
  have hq2 : q ≠ 2 := by
    intro heq
    subst q
    exact hq.not_dvd_of_lt (by decide) (by omega) (by decide : (2 : ℤ) ∣ 3 ^ 1 - 1)
  have hq5 : q ≠ 5 := by
    intro heq
    subst q
    exact hq.not_dvd_of_lt (by decide) (by omega) (by decide : (5 : ℤ) ∣ 3 ^ 4 - 1)
  have hq13 : q ≠ 13 := by
    intro heq
    subst q
    exact hq.not_dvd_of_lt (by decide) (by omega) (by decide : (13 : ℤ) ∣ 3 ^ 3 - 1)
  have hq3 : q ≠ 3 := by
    intro heq
    have hd : (q : ℤ) ∣ 3 ^ k - 1 := by simpa using hq.dvd
    rw [heq] at hd
    have hp : (3 : ℤ) ∣ 3 ^ k := dvd_pow_self _ (by omega)
    have h1 : (3 : ℤ) ∣ 1 := by
      convert dvd_sub hp hd using 1
      ring
    norm_num at h1
  exact ⟨q, by simpa using hq, by simp [hq2, hq3, hq5, hq13]⟩

private theorem two_primes_three_large (f : ℕ) (hf : 13 ≤ f) :
    ∃ q r, q.Prime ∧ r.Prime ∧ q ≠ r ∧
      q ∣ sigmaBiunitary (3 ^ f) ∧ r ∣ sigmaBiunitary (3 ^ f) ∧
      q ∉ ({2, 3, 5, 13} : Finset ℕ) ∧ r ∉ ({2, 3, 5, 13} : Finset ℕ) := by
  let t := f / 2 + 1
  let η := 1 - f % 2
  have hη : η ≤ 1 := by dsimp [η]; omega
  have ht : 7 ≤ t := by dsimp [t]; omega
  have hft : f + 1 + η = 2 * t := by dsimp [η, t]; omega
  obtain ⟨q, hq, hqout⟩ := primitive_minus_outside (t - η) (by omega)
  obtain ⟨r, hr', hmod⟩ := exists_primitivePrimeDivisor_pow_add_one 3 t
    (by decide) (by omega) (by omega) (by omega)
  have hr : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (3 : ℤ) ^ m + 1) t r := by
    simpa only [Nat.cast_ofNat] using hr'
  have hrlarge : 13 < r := by
    by_contra! h
    rw [Nat.mod_eq_of_lt (by omega : r < 2 * t)] at hmod
    have := hr.two_le
    omega
  have hrout : r ∉ ({2, 3, 5, 13} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hcast : ((2 * sigmaBiunitary (3 ^ f) : ℕ) : ℤ) =
      ((3 : ℤ) ^ t + 1) * ((3 : ℤ) ^ (t - η) - 1) := by
    rw [three_formula f t η hη hft (by omega), Nat.cast_mul,
      Nat.cast_add, Nat.cast_sub (by exact one_le_pow₀ (by decide : 1 ≤ (3 : ℕ))),
      Nat.cast_pow, Nat.cast_pow]
    norm_num
  have hqd : q ∣ sigmaBiunitary (3 ^ f) := by
    have h := dvd_mul_of_dvd_right hq.dvd ((3 : ℤ) ^ t + 1)
    rw [← hcast] at h
    have hn : q ∣ 2 * sigmaBiunitary (3 ^ f) := by exact_mod_cast h
    exact hq.prime.dvd_mul.mp hn |>.resolve_left (by
      intro hq2
      have heq := (Nat.prime_dvd_prime_iff_eq hq.prime Nat.prime_two).mp hq2
      subst q
      simp at hqout)
  have hrd : r ∣ sigmaBiunitary (3 ^ f) := by
    have h := dvd_mul_of_dvd_left hr.dvd ((3 : ℤ) ^ (t - η) - 1)
    rw [← hcast] at h
    have hn : r ∣ 2 * sigmaBiunitary (3 ^ f) := by exact_mod_cast h
    exact hr.prime.dvd_mul.mp hn |>.resolve_left (by
      intro h
      have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega)
  have hqr : q ≠ r := by
    intro heq
    have hqd := hq.dvd
    rw [heq] at hqd
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hη with hη0 | hη1
    · rw [hη0, Nat.sub_zero] at hqd
      have h2 : (r : ℤ) ∣ 2 := by
        convert dvd_sub hr.dvd hqd using 1
        ring
      have h2n : r ∣ 2 := by exact_mod_cast h2
      have := Nat.le_of_dvd (by decide : 0 < 2) h2n
      omega
    · rw [hη1] at hqd
      have h4 : (r : ℤ) ∣ 4 := by
        convert dvd_sub hr.dvd (dvd_mul_of_dvd_right hqd (3 : ℤ)) using 1
        rw [show (3 : ℤ) ^ t = 3 ^ (t - 1) * 3 by
          nth_rw 1 [show t = (t - 1) + 1 by omega]
          rw [pow_succ]]
        ring
      have h4n : r ∣ 4 := by exact_mod_cast h4
      have := Nat.le_of_dvd (by decide : 0 < 4) h4n
      omega
  exact ⟨q, r, hq.prime, hr.prime, hqr, hqd, hrd, hqout, hrout⟩

private theorem two_primes_three (f : ℕ) (hf : 9 ≤ f) :
    ∃ q r, q.Prime ∧ r.Prime ∧ q ≠ r ∧
      q ∣ sigmaBiunitary (3 ^ f) ∧ r ∣ sigmaBiunitary (3 ^ f) ∧
      q ∉ ({2, 3, 5, 13} : Finset ℕ) ∧ r ∉ ({2, 3, 5, 13} : Finset ℕ) := by
  by_cases hlarge : 13 ≤ f
  · exact two_primes_three_large f hlarge
  interval_cases f
  · have hs : sigmaBiunitary (3 ^ 9) = 29524 := by
      rw [prime_power_sum 3 9 Nat.prime_three (by decide)]
      norm_num [Finset.sum_range_succ]
    refine ⟨11, 61, by decide, by decide, by decide, ?_, ?_, by decide, by decide⟩ <;>
      rw [hs] <;> norm_num
  · have hs : sigmaBiunitary (3 ^ 10) = 88330 := by
      rw [prime_power_sum 3 10 Nat.prime_three (by decide)]
      norm_num [Finset.sum_range_succ]
    refine ⟨11, 73, by decide, by decide, by decide, ?_, ?_, by decide, by decide⟩ <;>
      rw [hs] <;> norm_num
  · have hs : sigmaBiunitary (3 ^ 11) = 265720 := by
      rw [prime_power_sum 3 11 Nat.prime_three (by decide)]
      norm_num [Finset.sum_range_succ]
    refine ⟨7, 73, by decide, by decide, by decide, ?_, ?_, by decide, by decide⟩ <;>
      rw [hs] <;> norm_num
  · have hs : sigmaBiunitary (3 ^ 12) = 796432 := by
      rw [prime_power_sum 3 12 Nat.prime_three (by decide)]
      norm_num [Finset.sum_range_succ]
    refine ⟨7, 547, by decide, by norm_num, by decide, ?_, ?_, by decide, by decide⟩ <;>
      rw [hs] <;> norm_num

private theorem not_five_odd_primes (n : ℕ) (hn : n ≠ 0)
    (hσ : sigmaBiunitary n = 3 * n) (he : n.factorization 2 = 4)
    (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h13 : 13 ∣ n) (q r : ℕ)
    (hq : q.Prime) (hr : r.Prime) (hqn : q ∣ n) (hrn : r ∣ n)
    (hqr : q ≠ r) (hqout : q ∉ ({2, 3, 5, 13} : Finset ℕ))
    (hrout : r ∉ ({2, 3, 5, 13} : Finset ℕ)) : False := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqout hrout
  have hd := odd_prime_product_dvd_sigma n hn {3, 5, 13, q, r} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact ⟨Nat.prime_three, h3, by decide⟩
    · exact ⟨Nat.prime_five, h5, by decide⟩
    · exact ⟨by decide, h13, by decide⟩
    · exact ⟨hq, hqn, hqout.1⟩
    · exact ⟨hr, hrn, hrout.1⟩)
  have hcard : ({3, 5, 13, q, r} : Finset ℕ).card = 5 := by
    simp [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
      hqr, hqout.2.1, hqout.2.2.1, hqout.2.2.2, hrout.2.1, hrout.2.2.1,
      hrout.2.2.2, ne_comm]
  rw [hcard] at hd
  exact not_thirtyTwo_dvd_sigmaBiunitary n hn hσ he hd

private theorem not_four_odd_primes (n : ℕ) (hn : n ≠ 0)
    (hσ : sigmaBiunitary n = 3 * n) (he : n.factorization 2 = 4)
    (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h13 : 13 ∣ n) (q : ℕ)
    (hq : q.Prime) (hqn : q ∣ n) (hqout : q ∉ ({2, 3, 5, 13} : Finset ℕ))
    (h4 : 4 ∣ sigmaBiunitary (3 ^ n.factorization 3)) : False := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqout
  let a (p : ℕ) := if p = 3 then 4 else 2
  have hs := subset_primes n hn {3, 5, 13, q} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨Nat.prime_three, h3⟩
    · exact ⟨Nat.prime_five, h5⟩
    · exact ⟨by decide, h13⟩
    · exact ⟨hq, hqn⟩)
  have hd := product_dvd_sigma n hn {3, 5, 13, q} hs a (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · simpa [a] using h4
    · simpa [a] using even_prime_power_sum 5 _ Nat.prime_five (by decide)
        (Nat.prime_five.dvd_iff_one_le_factorization hn |>.mp h5)
    · simpa [a] using even_prime_power_sum 13 _ (by decide) (by decide)
        ((show Nat.Prime 13 by decide).dvd_iff_one_le_factorization hn |>.mp h13)
    · simpa [a, hqout.2.1] using even_prime_power_sum _ _ hq hqout.1
        (hq.dvd_iff_one_le_factorization hn |>.mp hqn))
  norm_num [a, Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    hqout.2.1, hqout.2.2.1, hqout.2.2.2, ne_comm] at hd
  exact not_thirtyTwo_dvd_sigmaBiunitary n hn hσ he hd

private theorem not_prime_dvd_sigma_prime_power (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    ¬ p ∣ sigmaBiunitary (p ^ e) := by
  let k := (e + 1) / 2
  have hk : 0 < k := by dsimp [k]; omega
  have hs : (∑ i ∈ Finset.range k, p ^ i) =
      1 + p * ∑ i ∈ Finset.range (k - 1), p ^ i := by
    nth_rw 1 [show k = k - 1 + 1 by omega]
    rw [Finset.sum_range_succ']
    simp [pow_succ', Finset.mul_sum, add_comm]
  rw [prime_power_blocks p e hp he]
  change ¬ p ∣ (p ^ (e / 2 + 1) + 1) * ∑ i ∈ Finset.range k, p ^ i
  rw [hs, Nat.dvd_iff_mod_eq_zero]
  simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, Nat.mod_eq_of_lt hp.one_lt]

private theorem five_exponent_two_impossible (n : ℕ) (hn : n ≠ 0)
    (hσ : sigmaBiunitary n = 3 * n) (he : n.factorization 2 = 4)
    (hf : 5 ≤ n.factorization 3) (h5 : 5 ∣ n) (hg : n.factorization 5 = 2) : False := by
  have h3 : 3 ∣ n := (Nat.prime_three.dvd_iff_one_le_factorization hn).mpr (by omega)
  have h13 : 13 ∣ n := force_prime n 5 13 hn hσ Nat.prime_five h5 (by decide)
    (by decide) (by rw [hg, prime_power_two 5 Nat.prime_five]; decide)
  by_cases hlarge : 9 ≤ n.factorization 3
  · obtain ⟨q, r, hq, hr, hqr, hqd, hrd, hqout, hrout⟩ := two_primes_three _ hlarge
    have hq3 : q ≠ 3 := by
      intro h
      subst q
      simp at hqout
    have hr3 : r ≠ 3 := by
      intro h
      subst r
      simp at hrout
    exact not_five_odd_primes n hn hσ he h3 h5 h13 q r hq hr
      (force_prime n 3 q hn hσ Nat.prime_three h3 hq hq3 hqd)
      (force_prime n 3 r hn hσ Nat.prime_three h3 hr hr3 hrd) hqr hqout hrout
  have hcases : n.factorization 3 = 5 ∨ n.factorization 3 = 6 ∨
      n.factorization 3 = 7 ∨ n.factorization 3 = 8 := by omega
  rcases hcases with hf5 | hf6 | hf7 | hf8
  · have hs : sigmaBiunitary (3 ^ 5) = 364 := by
      rw [prime_power_sum 3 5 Nat.prime_three (by decide)]
      norm_num [Finset.sum_range_succ]
    have h7 : 7 ∣ n := force_prime n 3 7 hn hσ Nat.prime_three h3 (by decide)
      (by decide) (by rw [hf5, hs]; decide)
    exact not_four_odd_primes n hn hσ he h3 h5 h13 7 (by decide) h7 (by decide)
      (by rw [hf5, hs]; decide)
  · have h41 : 41 ∣ n := force_prime n 3 41 hn hσ Nat.prime_three h3 (by decide)
      (by decide) (by rw [hf6, sigma_three_six]; decide)
    have h41e : 1 ≤ n.factorization 41 :=
      (show Nat.Prime 41 by decide).dvd_iff_one_le_factorization hn |>.mp h41
    obtain ⟨q, hq, hqd, hqout⟩ := exists_prime_dvd_sigmaBiunitary_fortyOne_pow _ h41e
    have hq3 : q ≠ 3 := by
      intro h
      subst q
      simp at hqout
    have hq41 : 41 ≠ q := by
      intro h
      rw [← h] at hqd
      exact not_prime_dvd_sigma_prime_power 41 _ (by decide) h41e hqd
    exact not_five_odd_primes n hn hσ he h3 h5 h13 41 q (by decide) hq h41
      (force_prime n 41 q hn hσ (by decide) h41 hq hq3 hqd) hq41 (by decide) hqout
  · have hs : sigmaBiunitary (3 ^ 7) = 3280 := by
      rw [prime_power_sum 3 7 Nat.prime_three (by decide)]
      norm_num [Finset.sum_range_succ]
    have h41 : 41 ∣ n := force_prime n 3 41 hn hσ Nat.prime_three h3 (by decide)
      (by decide) (by rw [hf7, hs]; decide)
    exact not_four_odd_primes n hn hσ he h3 h5 h13 41 (by decide) h41 (by decide)
      (by rw [hf7, hs]; decide)
  · have hs : sigmaBiunitary (3 ^ 8) = 9760 := by
      rw [prime_power_sum 3 8 Nat.prime_three (by decide)]
      norm_num [Finset.sum_range_succ]
    have hd : 32 ∣ sigmaBiunitary (3 ^ n.factorization 3) := by
      rw [hf8, hs]
      decide
    exact not_thirtyTwo_dvd_sigmaBiunitary n hn hσ he
      (hd.trans (sigma_prime_power_dvd n 3 hn Nat.prime_three h3))

/-- **Biunitary triperfect numbers exactly divisible by $2^4$ and divisible by $3^5$ are prime
to $5$.** Let $N$ be a biunitary triperfect number, that is, a positive integer with
$\sigma^{**}(N) = 3N$, where $\sigma^{**}$ is the biunitary divisor sum. If the exact power of $2$
dividing $N$ is $2^4$ and $3^5$ divides $N$, then $5$ does not divide $N$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 15 (`jis-2025-25.4.5-lem-15`). -/
public theorem not_five_dvd_of_factorization_two_eq_four (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (he : N.factorization 2 = 4)
    (hf5 : 5 ≤ N.factorization 3) : ¬ 5 ∣ N := by
  intro h5
  exact five_exponent_two_impossible N hN.ne' hσ he hf5 h5
    (five_exponent_eq_two N hN.ne' hσ he hf5 h5)

end MetaMathlibExt
