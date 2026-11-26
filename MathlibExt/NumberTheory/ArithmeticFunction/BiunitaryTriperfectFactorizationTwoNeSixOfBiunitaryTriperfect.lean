/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Defs
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryFortyOne
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisorParity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# Excluding exponent six at two for biunitary triperfect numbers divisible by 27

A positive biunitary triperfect number divisible by 27 cannot have exponent six at two.
The proof uses multiplicativity, bounds for prime-power divisor sums, and divisibility
constraints at the primes 2, 3, 5, 7, 13, and 17.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 11.
-/

namespace MetaMathlibExt
open Finset

private theorem factorization_eq_of_unitary {a d p : ℕ} (hd : d ∈ a.unitaryDivisors)
    (hp : p.Prime) (hpd : p ∣ d) : a.factorization p = d.factorization p := by
  obtain ⟨hda, ha, hcop⟩ := Nat.mem_unitaryDivisors.mp hd
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    exact ha (zero_dvd_iff.mp hda)
  have hq0 : a / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd ha.bot_lt hda) hd0.bot_lt).ne'
  have hnq : ¬ p ∣ a / d := (hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hpd))
  conv_lhs => rw [← Nat.mul_div_cancel' hda]
  rw [Nat.factorization_mul hd0 hq0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnq, add_zero]

private theorem gcdUnitary_eq_one_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gcdUnitary a b = 1 ↔ ∀ p : ℕ, p.Prime → 0 < a.factorization p →
      a.factorization p ≠ b.factorization p := by
  constructor
  · intro h p hp he heq
    have hpa : p ^ a.factorization p ∈ a.unitaryDivisors := by
      exact Nat.mem_unitaryDivisors.mpr ⟨Nat.ordProj_dvd a p, ha,
        (Nat.coprime_ordCompl hp ha).pow_left _⟩
    have hpb : p ^ a.factorization p ∈ b.unitaryDivisors := by
      rw [heq]
      exact Nat.mem_unitaryDivisors.mpr ⟨Nat.ordProj_dvd b p, hb,
        (Nat.coprime_ordCompl hp hb).pow_left _⟩
    have hl := le_gcdUnitary hpa hpb
    rw [h] at hl
    exact (Nat.one_lt_pow he.ne' hp.one_lt).not_ge hl
  · intro h
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨hga, hgb⟩ := gcdUnitary_mem_unitaryDivisors ha hb
    have hfa := factorization_eq_of_unitary hga hp hpd
    have hfb := factorization_eq_of_unitary hgb hp hpd
    have hg0 : gcdUnitary a b ≠ 0 := (gcdUnitary_pos ha hb).ne'
    exact h p hp (hfa ▸ hp.factorization_pos_of_dvd hg0 hpd) (hfa.trans hfb.symm)

private theorem gcdUnitary_mul_eq_one {a b c d : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (habcd : (a * c).Coprime (b * d)) :
    gcdUnitary (a * b) (c * d) = 1 ↔ gcdUnitary a c = 1 ∧ gcdUnitary b d = 1 := by
  rw [gcdUnitary_eq_one_iff (mul_ne_zero ha hb) (mul_ne_zero hc hd),
    gcdUnitary_eq_one_iff ha hc, gcdUnitary_eq_one_iff hb hd]
  have hacb : a.Coprime b := (habcd.of_dvd_left (dvd_mul_right a c)).of_dvd_right
    (dvd_mul_right b d)
  have had : a.Coprime d := (habcd.of_dvd_left (dvd_mul_right a c)).of_dvd_right
    (dvd_mul_left d b)
  have hcb : c.Coprime b := (habcd.of_dvd_left (dvd_mul_left c a)).of_dvd_right
    (dvd_mul_right b d)
  have hcd : c.Coprime d := (habcd.of_dvd_left (dvd_mul_left c a)).of_dvd_right
    (dvd_mul_left d b)
  simp only [Nat.factorization_mul ha hb, Nat.factorization_mul hc hd, Finsupp.add_apply]
  constructor
  · intro h
    constructor
    · intro p hp he heq
      have hpa := hp.dvd_iff_one_le_factorization ha |>.mpr he
      have hpb : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
        (hp.coprime_iff_not_dvd.mp (hacb.of_dvd_left hpa))
      have hpd : d.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
        (hp.coprime_iff_not_dvd.mp (had.of_dvd_left hpa))
      exact h p hp (by omega) (by omega)
    · intro p hp he heq
      have hpb := hp.dvd_iff_one_le_factorization hb |>.mpr he
      have hpa : a.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
        (hp.coprime_iff_not_dvd.mp (hacb.symm.of_dvd_left hpb))
      have hpc : c.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
        (hp.coprime_iff_not_dvd.mp (hcb.symm.of_dvd_left hpb))
      exact h p hp (by omega) (by omega)
  · rintro ⟨h₁, h₂⟩ p hp he heq
    by_cases hpa : p ∣ a
    · have hpb : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
        (hp.coprime_iff_not_dvd.mp (hacb.of_dvd_left hpa))
      have hpd : d.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
        (hp.coprime_iff_not_dvd.mp (had.of_dvd_left hpa))
      exact h₁ p hp (by omega) (by omega)
    · have hfa := Nat.factorization_eq_zero_of_not_dvd hpa
      have hpb := hp.dvd_iff_one_le_factorization hb |>.mpr (by omega)
      have hpc : c.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
        (hp.coprime_iff_not_dvd.mp (hcb.symm.of_dvd_left hpb))
      exact h₂ p hp (by omega) (by omega)

private theorem biunitary_mul_iff {m n a b : ℕ} (hmn : m.Coprime n)
    (hm : m ≠ 0) (hn : n ≠ 0) (ham : a ∣ m) (hbn : b ∣ n) :
    a * b ∈ biunitaryDivisors (m * n) ↔
      a ∈ biunitaryDivisors m ∧ b ∈ biunitaryDivisors n := by
  have ha : a ≠ 0 := by intro h; subst a; exact hm (zero_dvd_iff.mp ham)
  have hb : b ≠ 0 := by intro h; subst b; exact hn (zero_dvd_iff.mp hbn)
  have hc : m / a ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hm.bot_lt ham) ha.bot_lt).ne'
  have hd : n / b ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn.bot_lt hbn) hb.bot_lt).ne'
  have hcop : (a * (m / a)).Coprime (b * (n / b)) := by
    rwa [Nat.mul_div_cancel' ham, Nat.mul_div_cancel' hbn]
  simp only [mem_biunitaryDivisors, ham, hbn, Nat.mul_dvd_mul ham hbn, true_and]
  rw [← Nat.div_mul_div_comm ham hbn, gcdUnitary_mul_eq_one ha hb hc hd hcop]
  simp [hm, hn]

private theorem sigmaBiunitary_mul {m n : ℕ} (hmn : m.Coprime n) :
    sigmaBiunitary (m * n) = sigmaBiunitary m * sigmaBiunitary n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [sigmaBiunitary]
  rw [sum_mul_sum, ← sum_product']
  symm
  refine sum_nbij' (fun x : ℕ × ℕ => x.1 * x.2) (fun d => (d.gcd m, d.gcd n))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    exact (biunitary_mul_iff hmn hm hn (dvd_of_mem_biunitaryDivisors ha)
      (dvd_of_mem_biunitaryDivisors hb)).mpr ⟨ha, hb⟩
  · intro d hd
    have hdmn := dvd_of_mem_biunitaryDivisors hd
    have hsplit : d.gcd m * d.gcd n = d := by
      rw [← Nat.Coprime.gcd_mul d hmn, Nat.gcd_eq_left hdmn]
    exact mem_product.mpr ((biunitary_mul_iff hmn hm hn (Nat.gcd_dvd_right d m)
      (Nat.gcd_dvd_right d n)).mp (hsplit.symm ▸ hd))
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    have ham := dvd_of_mem_biunitaryDivisors ha
    have hbn := dvd_of_mem_biunitaryDivisors hb
    have hbm := hmn.symm.of_dvd_left hbn
    have han := hmn.of_dvd_left ham
    simp only [Prod.mk.injEq]
    exact ⟨by rw [Nat.Coprime.gcd_mul_right_cancel a hbm, Nat.gcd_eq_left ham],
      by rw [Nat.Coprime.gcd_mul_left_cancel b han, Nat.gcd_eq_left hbn]⟩
  · intro d hd
    rw [← Nat.Coprime.gcd_mul d hmn,
      Nat.gcd_eq_left (dvd_of_mem_biunitaryDivisors hd)]
  · rintro ⟨a, b⟩ _
    rfl

private theorem sigmaBiunitary_ge (n : ℕ) (hn : n ≠ 0) : n ≤ sigmaBiunitary n := by
  rw [sigmaBiunitary]
  apply single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
  refine mem_biunitaryDivisors.mpr ⟨dvd_rfl, hn, ?_⟩
  rw [gcdUnitary, Nat.div_self hn.bot_lt,
    show (1 : ℕ).unitaryDivisors = {1} from by decide,
    inter_singleton_of_mem (by simp [hn])]
  simp

private theorem sigmaBiunitary_ordProj_dvd (N p : ℕ) (hN : N ≠ 0) (hp : p.Prime) :
    sigmaBiunitary (p ^ N.factorization p) ∣ sigmaBiunitary N := by
  have hmul := sigmaBiunitary_mul ((Nat.coprime_ordCompl hp hN).pow_left
    (N.factorization p))
  rw [Nat.ordProj_mul_ordCompl_eq_self N p] at hmul
  rw [hmul]
  exact dvd_mul_right _ _

private theorem sigmaBiunitary_ratio_prod_le (s : Finset ℕ) (N : ℕ) (hN : N ≠ 0)
    (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, ((sigmaBiunitary (p ^ N.factorization p) : ℚ) / (p : ℚ) ^ N.factorization p) ≤
      (sigmaBiunitary N : ℚ) / N := by
  induction s using Finset.induction_on generalizing N with
  | empty =>
    simp only [prod_empty]
    rw [le_div_iff₀ (by exact_mod_cast hN.bot_lt), one_mul]
    exact_mod_cast sigmaBiunitary_ge N hN
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self p s)
    have hM : ordCompl[p] N ≠ 0 := (Nat.ordCompl_pos p hN).ne'
    have hfac (q : ℕ) (hq : q ∈ s) : (ordCompl[p] N).factorization q = N.factorization q := by
      rw [Nat.factorization_ordCompl, Finsupp.erase_ne (ne_of_mem_of_not_mem hq hp)]
    have hprod : (∏ q ∈ s, ((sigmaBiunitary (q ^ (ordCompl[p] N).factorization q) : ℚ) /
        (q : ℚ) ^ (ordCompl[p] N).factorization q)) =
        ∏ q ∈ s, ((sigmaBiunitary (q ^ N.factorization q) : ℚ) /
          (q : ℚ) ^ N.factorization q) := by
      apply prod_congr rfl
      intro q hq
      rw [hfac q hq]
    have hsplit : (sigmaBiunitary N : ℚ) / N =
        ((sigmaBiunitary (p ^ N.factorization p) : ℚ) / (p : ℚ) ^ N.factorization p) *
          ((sigmaBiunitary (ordCompl[p] N) : ℚ) / ((ordCompl[p] N : ℕ) : ℚ)) := by
      rw [div_mul_div_comm]
      have hmul := sigmaBiunitary_mul ((Nat.coprime_ordCompl hprime hN).pow_left
        (N.factorization p))
      rw [Nat.ordProj_mul_ordCompl_eq_self N p] at hmul
      rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul,
        Nat.ordProj_mul_ordCompl_eq_self N p, ← hmul]
    rw [prod_insert hp, hsplit]
    have hpos : (0 : ℚ) < p := by exact_mod_cast hprime.pos
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos hpos _)))
    rw [← hprod]
    exact ih (ordCompl[p] N) hM (fun q hq => hs q (mem_insert_of_mem hq))

private theorem sigmaBiunitary_ratio_list_bound (N : ℕ) (hN : N ≠ 0)
    (hσ : sigmaBiunitary N = 3 * N) (l : List (ℕ × ℚ))
    (hl : (l.map Prod.fst).Nodup) (hp : ∀ x ∈ l, x.1.Prime)
    (hb0 : ∀ x ∈ l, 0 ≤ x.2)
    (hb : ∀ x ∈ l, x.2 ≤ (sigmaBiunitary (x.1 ^ N.factorization x.1) : ℚ) /
      (x.1 : ℚ) ^ N.factorization x.1) : (l.map Prod.snd).prod ≤ 3 := by
  have hl' := List.Nodup.of_map Prod.fst hl
  rw [← List.prod_toFinset Prod.snd hl']
  have hi : Set.InjOn Prod.fst (l.toFinset : Set (ℕ × ℚ)) := by
    intro x hx y hy heq
    exact (List.nodup_map_iff_inj_on hl').mp hl x (List.mem_toFinset.mp hx)
      y (List.mem_toFinset.mp hy) heq
  have hle := Finset.prod_le_prod₀ (fun x hx => hb0 x (List.mem_toFinset.mp hx))
    (fun x hx => hb x (List.mem_toFinset.mp hx))
  apply hle.trans
  rw [← Finset.prod_image (f := fun p : ℕ => (sigmaBiunitary (p ^ N.factorization p) : ℚ) /
    (p : ℚ) ^ N.factorization p) hi]
  have h := sigmaBiunitary_ratio_prod_le (l.toFinset.image Prod.fst) N hN (by
    intro p hp'
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hp'
    exact hp x (List.mem_toFinset.mp hx))
  simpa [hσ, hN] using h

private theorem biunitary_pow_iff {p g i : ℕ} (hp : p.Prime) (hg : 0 < g) (hi : i ≤ g) :
    gcdUnitary (p ^ i) (p ^ g / p ^ i) = 1 ↔ 2 * i ≠ g := by
  rw [Nat.pow_div hi hp.pos, gcdUnitary_eq_one_iff
    (pow_ne_zero i hp.ne_zero) (pow_ne_zero (g - i) hp.ne_zero)]
  constructor
  · intro h heq
    have hi0 : 0 < i := by omega
    have hh := h p hp (by simpa only [hp.factorization_pow, Finsupp.single_eq_same] using hi0)
    simp only [hp.factorization_pow, Finsupp.single_eq_same] at hh
    omega
  · intro h q hq hqi heq
    have hqp : q = p := by
      by_contra hne
      simp [hp.factorization_pow, hne] at hqi
    subst q
    simp only [hp.factorization_pow, Finsupp.single_eq_same] at heq
    omega

private theorem sigmaBiunitary_prime_pow_sum {p g : ℕ} (hp : p.Prime) (hg : 0 < g) :
    sigmaBiunitary (p ^ g) = ∑ i ∈ range (g + 1), if 2 * i = g then 0 else p ^ i := by
  rw [sigmaBiunitary, biunitaryDivisors, sum_filter, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro i hi
  simp [biunitary_pow_iff hp hg (Nat.le_of_lt_succ (mem_range.mp hi)), ite_not]

private theorem sigmaBiunitary_partial_ratio (p e : ℕ) (hp : p.Prime) (he : 0 < e)
    (s : Finset ℕ) (hs : ∀ i ∈ s, i ≤ e ∧ 2 * (e - i) ≠ e) :
    ∑ i ∈ s, 1 / (p : ℚ) ^ i ≤ (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e := by
  have hpos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  let w (i : ℕ) : ℚ := if 2 * (e - i) = e then 0 else 1 / (p : ℚ) ^ i
  have hnormalized : (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e =
      ∑ i ∈ range (e + 1), w i := by
    rw [sigmaBiunitary_prime_pow_sum hp he, Nat.cast_sum, sum_div, ← sum_range_reflect]
    refine sum_congr rfl fun i hi => ?_
    have hie : i ≤ e := Nat.le_of_lt_succ (mem_range.mp hi)
    simp only [Nat.add_sub_cancel, Nat.cast_ite, Nat.cast_zero, Nat.cast_pow, w]
    split
    · simp
    · apply (div_eq_div_iff (pow_ne_zero _ hpos.ne') (pow_ne_zero _ hpos.ne')).2
      rw [← pow_add, Nat.sub_add_cancel hie, one_mul]
  rw [hnormalized]
  calc
    _ = ∑ i ∈ s, w i := sum_congr rfl fun i hi => by simp [w, (hs i hi).2]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (fun i hi => mem_range.mpr (Nat.lt_succ_of_le (hs i hi).1))
      (fun i _ _ => by
        dsimp [w]
        split
        · exact le_rfl
        · exact div_nonneg zero_le_one (le_of_lt (pow_pos hpos i)))

private theorem sigmaBiunitary_three_ratio (f : ℕ) (hf : 3 ≤ f) (hf4 : f ≠ 4) :
    (1066 / 729 : ℚ) ≤ (sigmaBiunitary (3 ^ f) : ℚ) / (3 : ℚ) ^ f := by
  by_cases hsmall : f ≤ 6
  · have h5 := sigmaBiunitary_prime_pow_sum (p := 3) (g := 5) (by decide) (by decide)
    norm_num [Finset.sum_range_succ] at h5
    have h6 := sigmaBiunitary_prime_pow_sum (p := 3) (g := 6) (by decide) (by decide)
    norm_num [Finset.sum_range_succ] at h6
    interval_cases f <;> norm_num [sigmaBiunitary_twentySeven, h5, h6] at *
  · have h := sigmaBiunitary_partial_ratio 3 f (by decide) (by omega) {0, 1, 2, 3} (by
      intro i hi
      simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> omega)
    norm_num [Finset.sum_insert] at h
    linarith

private theorem sigmaBiunitary_prod_dvd (s : Finset ℕ) (N : ℕ) (hN : N ≠ 0)
    (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, sigmaBiunitary (p ^ N.factorization p) ∣ sigmaBiunitary N := by
  induction s using Finset.induction_on generalizing N with
  | empty => simp
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self p s)
    have hM : ordCompl[p] N ≠ 0 := (Nat.ordCompl_pos p hN).ne'
    have hprod : (∏ q ∈ s, sigmaBiunitary (q ^ (ordCompl[p] N).factorization q)) =
        ∏ q ∈ s, sigmaBiunitary (q ^ N.factorization q) := by
      apply prod_congr rfl
      intro q hq
      rw [Nat.factorization_ordCompl, Finsupp.erase_ne (ne_of_mem_of_not_mem hq hp)]
    have hmul := sigmaBiunitary_mul ((Nat.coprime_ordCompl hprime hN).pow_left
      (N.factorization p))
    rw [Nat.ordProj_mul_ordCompl_eq_self N p] at hmul
    rw [prod_insert hp, hmul, ← hprod]
    exact Nat.mul_dvd_mul dvd_rfl
      (ih (ordCompl[p] N) hM (fun q hq => hs q (mem_insert_of_mem hq)))

private theorem sigmaBiunitary_divisibility_list (N : ℕ) (hN : N ≠ 0)
    (l : List (ℕ × ℕ)) (hl : (l.map Prod.fst).Nodup) (hp : ∀ x ∈ l, x.1.Prime)
    (hd : ∀ x ∈ l, x.2 ∣ sigmaBiunitary (x.1 ^ N.factorization x.1)) :
    (l.map Prod.snd).prod ∣ sigmaBiunitary N := by
  have hl' := List.Nodup.of_map Prod.fst hl
  rw [← List.prod_toFinset Prod.snd hl']
  have hi : Set.InjOn Prod.fst (l.toFinset : Set (ℕ × ℕ)) := by
    intro x hx y hy heq
    exact (List.nodup_map_iff_inj_on hl').mp hl x (List.mem_toFinset.mp hx)
      y (List.mem_toFinset.mp hy) heq
  apply (prod_dvd_prod_of_dvd Prod.snd (fun x => sigmaBiunitary (x.1 ^ N.factorization x.1))
    (fun x hx => hd x (List.mem_toFinset.mp hx))).trans
  rw [← Finset.prod_image (f := fun p : ℕ => sigmaBiunitary (p ^ N.factorization p)) hi]
  exact sigmaBiunitary_prod_dvd (l.toFinset.image Prod.fst) N hN (by
    intro p hp'
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hp'
    exact hp x (List.mem_toFinset.mp hx))

private theorem two_dvd_sigmaBiunitary_odd_prime_pow (p e : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 0 < e) : 2 ∣ sigmaBiunitary (p ^ e) := by
  rw [← even_iff_two_dvd, ← Nat.not_odd_iff_even, odd_sigmaBiunitary_iff _ (pow_pos hp.pos e)]
  rintro ⟨k, hk⟩
  have hpd : p ∣ p ^ e := dvd_pow_self p he.ne'
  rw [hk] at hpd
  have hpdiv := hp.dvd_of_dvd_pow hpd
  exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hpdiv |>.resolve_left hp.ne_one)

private theorem sigmaBiunitary_prime_pow_two (p : ℕ) (hp : p.Prime) :
    sigmaBiunitary (p ^ 2) = p ^ 2 + 1 := by
  rw [sigmaBiunitary_prime_pow_sum hp (by decide)]
  simp [Finset.sum_range_succ, add_comm]

private theorem sigmaBiunitary_sixtyFour : sigmaBiunitary (2 ^ 6) = 119 := by
  have h := sigmaBiunitary_prime_pow_sum (p := 2) (g := 6) (by decide) (by decide)
  norm_num [Finset.sum_range_succ] at h
  exact h

private theorem prime_dvd_of_sigmaBiunitary_prime_pow (N p q : ℕ) (hN : N ≠ 0)
    (hσ : sigmaBiunitary N = 3 * N) (hp : p.Prime) (hq : q.Prime) (hq3 : q ≠ 3)
    (hd : q ∣ sigmaBiunitary (p ^ N.factorization p)) : q ∣ N := by
  have h := hd.trans (sigmaBiunitary_ordProj_dvd N p hN hp)
  rw [hσ] at h
  exact (hq.dvd_mul.mp h).resolve_left
    (fun hqdiv => hq3 ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hqdiv |>.resolve_left
      hq.ne_one))

private theorem factorization_seven_eq_two (N : ℕ) (hN : N ≠ 0)
    (hσ : sigmaBiunitary N = 3 * N)
    (h2 : (sigmaBiunitary (2 ^ N.factorization 2) : ℚ) /
      (2 : ℚ) ^ N.factorization 2 = 119 / 64)
    (h3 : (112 / 81 : ℚ) ≤ (sigmaBiunitary (3 ^ N.factorization 3) : ℚ) /
      (3 : ℚ) ^ N.factorization 3)
    (h7pos : 0 < N.factorization 7) (h17pos : 0 < N.factorization 17) :
    N.factorization 7 = 2 := by
  have bound := sigmaBiunitary_ratio_list_bound N hN hσ
  by_contra hne7
  have h7 : (8 / 7 : ℚ) ≤ (sigmaBiunitary (7 ^ N.factorization 7) : ℚ) /
      (7 : ℚ) ^ N.factorization 7 := by
    convert (sigmaBiunitary_prime_pow_div_ge 7 (N.factorization 7)
      (by decide) h7pos).2.1 hne7 using 1
    norm_num
  by_cases he17 : N.factorization 17 = 2
  · have h5dvd : 5 ∣ N := prime_dvd_of_sigmaBiunitary_prime_pow N 17 5 hN hσ
      (by decide) (by decide) (by decide) (by
        rw [he17, sigmaBiunitary_prime_pow_two 17 (by decide)]
        decide)
    have h5pos : 0 < N.factorization 5 := (Nat.Prime.dvd_iff_one_le_factorization
      (by decide : Nat.Prime 5) hN).mp h5dvd
    have h5 : (26 / 25 : ℚ) ≤ (sigmaBiunitary (5 ^ N.factorization 5) : ℚ) /
        (5 : ℚ) ^ N.factorization 5 := by
      convert (sigmaBiunitary_prime_pow_div_ge 5 (N.factorization 5)
        (by decide) h5pos).1 using 1
      norm_num
    have h := bound [(2, 119 / 64), (3, 112 / 81), (5, 26 / 25), (7, 8 / 7)]
      (by decide) (by decide) (by norm_num [List.mem_cons]) (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact h2.ge
        · exact h3
        · exact h5
        · exact h7)
    norm_num at h
  · have h17 : (18 / 17 : ℚ) ≤ (sigmaBiunitary (17 ^ N.factorization 17) : ℚ) /
        (17 : ℚ) ^ N.factorization 17 := by
      convert (sigmaBiunitary_prime_pow_div_ge 17 (N.factorization 17)
        (by decide) h17pos).2.1 he17 using 1
      norm_num
    have h := bound [(2, 119 / 64), (3, 112 / 81), (7, 8 / 7), (17, 18 / 17)]
      (by decide) (by decide) (by norm_num [List.mem_cons]) (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact h2.ge
        · exact h3
        · exact h7
        · exact h17)
    norm_num at h

/-- **No biunitary triperfect number divisible by $27$ is exactly divisible by $2^6$.** Let $N$
be a biunitary triperfect number, that is, a positive integer with $\sigma^{**}(N) = 3N$, where
$\sigma^{**}$ is the biunitary divisor sum. If $3^3$ divides $N$, then the exact power of $2$
dividing $N$ is not $2^6$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 11 (`jis-2025-25.4.5-lem-11`). -/
public theorem factorization_two_ne_six_of_biunitaryTriperfect (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3) :
    N.factorization 2 ≠ 6 := by
  intro he
  have h2 : (sigmaBiunitary (2 ^ N.factorization 2) : ℚ) /
      (2 : ℚ) ^ N.factorization 2 = 119 / 64 := by
    rw [he, sigmaBiunitary_sixtyFour]
    norm_num
  have h3 : (112 / 81 : ℚ) ≤ (sigmaBiunitary (3 ^ N.factorization 3) : ℚ) /
      (3 : ℚ) ^ N.factorization 3 := by
    have h := (sigmaBiunitary_prime_pow_div_ge 3 (N.factorization 3) (by decide) (by omega)).2.2 hf
    norm_num at h
    exact h
  have h7dvd : 7 ∣ N := prime_dvd_of_sigmaBiunitary_prime_pow N 2 7 hN.ne' hσ
    (by decide) (by decide) (by decide) (by rw [he, sigmaBiunitary_sixtyFour]; decide)
  have h17dvd : 17 ∣ N := prime_dvd_of_sigmaBiunitary_prime_pow N 2 17 hN.ne' hσ
    (by decide) (by decide) (by decide) (by rw [he, sigmaBiunitary_sixtyFour]; decide)
  have h7pos : 0 < N.factorization 7 := (Nat.Prime.dvd_iff_one_le_factorization
    (by decide : Nat.Prime 7) hN.ne').mp h7dvd
  have h17pos : 0 < N.factorization 17 := (Nat.Prime.dvd_iff_one_le_factorization
    (by decide : Nat.Prime 17) hN.ne').mp h17dvd
  have bound := sigmaBiunitary_ratio_list_bound N hN.ne' hσ
  have divides := sigmaBiunitary_divisibility_list N hN.ne'
  have he7 := factorization_seven_eq_two N hN.ne' hσ h2 h3 h7pos h17pos
  have h25sigma : 25 ∣ sigmaBiunitary N := by
    apply dvd_trans _ (sigmaBiunitary_ordProj_dvd N 7 hN.ne' (by decide))
    rw [he7, sigmaBiunitary_prime_pow_two 7 (by decide)]
    decide
  have h25 : 25 ∣ N := (by decide : Nat.Coprime 25 3).dvd_of_dvd_mul_left (hσ ▸ h25sigma)
  have h5ge : 2 ≤ N.factorization 5 :=
    (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 5) hN.ne').mp h25
  have h5even : 2 ∣ sigmaBiunitary (5 ^ N.factorization 5) :=
    two_dvd_sigmaBiunitary_odd_prime_pow 5 _ (by decide) (by decide) (by omega)
  have h17even : 2 ∣ sigmaBiunitary (17 ^ N.factorization 17) :=
    two_dvd_sigmaBiunitary_odd_prime_pow 17 _ (by decide) (by decide) h17pos
  have hf4 : N.factorization 3 ≠ 4 := by
    intro hf4
    have h := divides [(3, 16), (7, 2), (5, 2), (17, 2)] (by decide) (by decide) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [hf4]
        change 16 ∣ sigmaBiunitary (3 ^ 4)
        rw [sigmaBiunitary_prime_pow_sum (by decide : Nat.Prime 3) (by decide)]
        norm_num [Finset.sum_range_succ]
      · rw [he7, sigmaBiunitary_prime_pow_two 7 (by decide)]
        decide
      · exact h5even
      · exact h17even)
    norm_num only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Prod.snd, mul_one] at h
    have hσ0 : sigmaBiunitary N ≠ 0 := by
      rw [hσ]
      exact mul_ne_zero (by decide) hN.ne'
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization (k := 7) Nat.prime_two hσ0).mp h
    rw [hσ, Nat.factorization_mul (by decide) hN.ne', Finsupp.add_apply] at hle
    norm_num [he, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ (2 : ℕ) ∣ 3)] at hle
  have h3' := sigmaBiunitary_three_ratio (N.factorization 3) hf hf4
  have h7 : (sigmaBiunitary (7 ^ N.factorization 7) : ℚ) /
      (7 : ℚ) ^ N.factorization 7 = 50 / 49 := by
    rw [he7, sigmaBiunitary_prime_pow_two 7 (by decide)]
    norm_num
  have he5 : N.factorization 5 = 2 := by
    by_contra hne5
    have h5 : (6 / 5 : ℚ) ≤ (sigmaBiunitary (5 ^ N.factorization 5) : ℚ) /
        (5 : ℚ) ^ N.factorization 5 := by
      convert (sigmaBiunitary_prime_pow_div_ge 5 (N.factorization 5)
        (by decide) (by omega)).2.1 hne5 using 1
      norm_num
    have h := bound [(2, 119 / 64), (3, 1066 / 729), (7, 50 / 49), (5, 6 / 5)]
      (by decide) (by decide) (by norm_num [List.mem_cons]) (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact h2.ge
        · exact h3'
        · exact h7.ge
        · exact h5)
    norm_num at h
  have h13dvd : 13 ∣ N := prime_dvd_of_sigmaBiunitary_prime_pow N 5 13 hN.ne' hσ
    (by decide) (by decide) (by decide) (by
      rw [he5, sigmaBiunitary_prime_pow_two 5 (by decide)]
      decide)
  have h13pos : 0 < N.factorization 13 := (Nat.Prime.dvd_iff_one_le_factorization
    (by decide : Nat.Prime 13) hN.ne').mp h13dvd
  have he13 : N.factorization 13 ≠ 2 := by
    intro he13
    have h := divides [(7, 25), (13, 5)] (by decide) (by decide) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [he7, sigmaBiunitary_prime_pow_two 7 (by decide)]
        decide
      · rw [he13, sigmaBiunitary_prime_pow_two 13 (by decide)]
        decide)
    norm_num only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Prod.snd, mul_one] at h
    have hd : 125 ∣ N := (by decide : Nat.Coprime 125 3).dvd_of_dvd_mul_left (hσ ▸ h)
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization (k := 3)
      (by decide : Nat.Prime 5) hN.ne').mp hd
    omega
  have h5 : (sigmaBiunitary (5 ^ N.factorization 5) : ℚ) /
      (5 : ℚ) ^ N.factorization 5 = 26 / 25 := by
    rw [he5, sigmaBiunitary_prime_pow_two 5 (by decide)]
    norm_num
  have h13 : (14 / 13 : ℚ) ≤ (sigmaBiunitary (13 ^ N.factorization 13) : ℚ) /
      (13 : ℚ) ^ N.factorization 13 := by
    convert (sigmaBiunitary_prime_pow_div_ge 13 (N.factorization 13)
      (by decide) h13pos).2.1 he13 using 1
    norm_num
  have h := bound [(2, 119 / 64), (3, 1066 / 729), (7, 50 / 49), (5, 26 / 25), (13, 14 / 13)]
    (by decide) (by decide) (by norm_num [List.mem_cons]) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h2.ge
      · exact h3'
      · exact h7.ge
      · exact h5.ge
      · exact h13)
  norm_num at h

end MetaMathlibExt
