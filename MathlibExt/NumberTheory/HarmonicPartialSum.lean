/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Int

namespace MetaMathlibExt

@[expose] public section

/-! # Partial sums of harmonic numbers are never integers
-/

/-- Identity `∑_{ν=2}^n H_ν = (n+1) * (H_n - 1)` (equation (1.2) of the source). -/
private lemma sum_Icc_harmonic (n : ℕ) (hn : 1 ≤ n) :
    ∑ ν ∈ Finset.Icc 2 n, harmonic ν = ((n + 1 : ℕ) : ℚ) * (harmonic n - 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hI : Finset.Icc 2 1 = ∅ := by decide
    have h1 : harmonic 1 = 1 := by
      unfold harmonic
      norm_num [Finset.sum_range_succ]
    rw [hI, Finset.sum_empty, h1]
    norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1) harmonic, ih, harmonic_succ]
    have hne : (n : ℚ) + 1 ≠ 0 := by
      have h1n : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      have hpos : (0 : ℚ) < (n : ℚ) + 1 := by linarith
      exact ne_of_gt hpos
    push_cast
    field_simp
    ring

/-- The shifted harmonic number `H_n - 1` as a sum of reciprocals from `2`. -/
private lemma harmonic_sub_one (n : ℕ) (hn : 1 ≤ n) :
    harmonic n - 1 = ∑ j ∈ Finset.Icc 2 n, ((j : ℚ))⁻¹ := by
  have hH : harmonic n = ∑ j ∈ Finset.Icc 1 n, ((j : ℚ))⁻¹ := harmonic_eq_sum_Icc
  have hins : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1 : ((((1 : ℕ))) : ℚ)⁻¹ = 1 := by norm_num
  rw [hH, hins, Finset.sum_insert (by simp), h1]
  ring

/-- The `2`-adic valuation of `H_n - 1` for `n ≥ 2`. -/
private lemma padicValRat_two_harmonic_sub_one {n : ℕ} (hn : 2 ≤ n) :
    padicValRat 2 (harmonic n - 1) = -((((Nat.log 2 n : ℕ))) : ℤ) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < harmonic n := harmonic_pos hn0
  have hlog : 0 < Nat.log 2 n := Nat.log_pos one_lt_two hn
  have hlogz : (0 : ℤ) < ((((Nat.log 2 n : ℕ))) : ℤ) := by exact_mod_cast hlog
  have hR : harmonic n - 1 = ∑ j ∈ Finset.Icc 2 n, ((j : ℚ))⁻¹ :=
    harmonic_sub_one n (by omega)
  have hne : harmonic n - 1 ≠ 0 := by
    rw [hR]
    apply ne_of_gt
    refine Finset.sum_pos (fun i hi => ?_) ⟨2, Finset.mem_Icc.mpr ⟨le_refl 2, hn⟩⟩
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    have hpos : (0 : ℚ) < ((i : ℚ)) := by
      have hi0 : 0 < i := by omega
      exact_mod_cast hi0
    exact inv_pos.mpr hpos
  have hval : padicValRat 2 (harmonic n) ≠ padicValRat 2 (-1 : ℚ) := by
    rw [padicValRat_two_harmonic, padicValRat.neg, padicValRat.one]
    omega
  have hsum : harmonic n + (-1 : ℚ) ≠ 0 := by rwa [← sub_eq_add_neg]
  rw [sub_eq_add_neg,
    padicValRat.add_eq_min hsum (ne_of_gt hnpos) (by norm_num) hval,
    padicValRat_two_harmonic, padicValRat.neg, padicValRat.one]
  exact min_eq_left (neg_nonpos.mpr (le_of_lt hlogz))

/-- A finite sum of rationals of nonnegative `p`-adic valuation has nonnegative valuation. -/
private lemma padicValRat_nonneg_of_sum_nonneg {p : ℕ} [Fact (Nat.Prime p)] {S : Finset ℕ}
    {F : ℕ → ℚ} (hF : ∀ i ∈ S, 0 ≤ padicValRat p (F i)) :
    0 ≤ padicValRat p (∑ i ∈ S, F i) := by
  revert hF
  refine Finset.induction_on S ?_ ?_
  · intro hF
    simp
  · intro a s has ih hF
    rw [Finset.sum_insert has]
    by_cases h0 : F a + ∑ i ∈ s, F i = 0
    · simp [h0]
    · calc (0 : ℤ) ≤ min (padicValRat p (F a)) (padicValRat p (∑ i ∈ s, F i)) :=
            le_min (hF a (Finset.mem_insert_self a s))
              (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))
          _ ≤ padicValRat p (F a + ∑ i ∈ s, F i) :=
            padicValRat.min_le_padicValRat_add h0

/--
**Sums of harmonic numbers starting from the second are not integers.** For every natural number
$n \ge 2$, the sum $\sum_{\nu=2}^{n} H_\nu$ is not an integer, where
$H_\nu = \sum_{j=1}^{\nu} 1/j$ is the $\nu$-th harmonic number, viewed as a rational number.

The source proves this via its identity $\sum_{\nu=2}^n H_\nu = (n+1)(H_n - 1)$ (equation (1.2)),
reducing to the non-integrality of $(n+1) H_n$, in the spirit of Theisinger's theorem that $H_n$
itself is never an integer for $n > 1$.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a Combinatorial
Identity Involving Harmonic Numbers," Journal of Integer Sequences 29
(2026), Article 26.4.8, Theorem (label T3), lines 460–462,
https://cs.uwaterloo.ca/journals/JIS/VOL29/Alzer/alzer22.tex
Proves `Wanted` entry `harmonic_partial_sum_not_int`.
-/
theorem harmonic_partial_sum_not_int
    (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ k : ℤ, (k : ℚ) = ∑ ν ∈ Finset.Icc 2 n, harmonic ν := by
  have h1n : 1 ≤ n := by omega
  rw [sum_Icc_harmonic n h1n]
  have hcast : ((n + 1 : ℕ) : ℚ) ≠ 0 := by
    have h10 : n + 1 ≠ 0 := by omega
    exact_mod_cast h10
  have hH1 : harmonic n - 1 ≠ 0 := by
    rw [harmonic_sub_one n (by omega)]
    apply ne_of_gt
    refine Finset.sum_pos (fun i hi => ?_) ⟨2, Finset.mem_Icc.mpr ⟨le_refl 2, hn⟩⟩
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    have hpos : (0 : ℚ) < ((i : ℚ)) := by
      have hi0 : 0 < i := by omega
      exact_mod_cast hi0
    exact inv_pos.mpr hpos
  have hSne : ((n + 1 : ℕ) : ℚ) * (harmonic n - 1) ≠ 0 := mul_ne_zero hcast hH1
  have hV2 := padicValRat_two_harmonic_sub_one hn
  have hvalS : padicValRat 2 (((n + 1 : ℕ) : ℚ) * (harmonic n - 1))
      = (((padicValNat 2 (n + 1) : ℕ)) : ℤ)
        + -((((Nat.log 2 n : ℕ))) : ℤ) := by
    rw [padicValRat.mul hcast hH1, padicValRat.of_nat, hV2]
  by_cases hpow : ∃ m, n + 1 = 2 ^ m
  · -- When `n + 1` is a power of two, the `2`-adic argument fails, so use a
    -- Bertrand prime instead.
    obtain ⟨m, hm⟩ := hpow
    by_cases hn3 : n = 3
    · subst hn3
      have h3 : harmonic 3 = 11 / 6 := by
        unfold harmonic
        norm_num [Finset.sum_range_succ]
      intro hcon
      obtain ⟨k, hk⟩ := hcon
      rw [h3] at hk
      have h4 : ((((3 + 1 : ℕ))) : ℚ) = 4 := by norm_num
      rw [h4] at hk
      have h10q : (3 : ℚ) * (k : ℚ) = 10 := by linarith
      have h10 : (3 : ℤ) * k = 10 := by exact_mod_cast h10q
      omega
    · have hm2 : 2 ≤ m := by
        rcases Nat.lt_or_ge m 2 with h | h
        · interval_cases m
          · rw [pow_zero] at hm
            omega
          · rw [pow_one] at hm
            omega
        · exact h
      have hn4 : 4 ≤ n := by
        have h4m : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
        have h42 : (4 : ℕ) = 2 ^ 2 := by norm_num
        omega
      have hq0 : n / 2 ≠ 0 := by omega
      obtain ⟨p, hpP, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) hq0
      have : Fact (Nat.Prime p) := ⟨hpP⟩
      have hp2 : 2 < p := by
        have hq2 : 2 ≤ n / 2 := by omega
        omega
      have hple : p ≤ n := by
        have h1 : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
        omega
      have h2p : n < 2 * p := by omega
      have hpmem : p ∈ Finset.Icc 2 n :=
        Finset.mem_Icc.mpr ⟨hpP.two_le, hple⟩
      have hB := harmonic_sub_one n (by omega)
      have hsplit : (∑ j ∈ Finset.Icc 2 n, ((j : ℚ))⁻¹)
          = ((p : ℚ))⁻¹ + ∑ j ∈ (Finset.Icc 2 n).erase p, ((j : ℚ))⁻¹ :=
        (Finset.add_sum_erase _ _ hpmem).symm
      have hFp : padicValRat p (((p : ℚ)))⁻¹ = -1 := by
        rw [padicValRat.inv, padicValRat.self hpP.one_lt]
      have h2mem : 2 ∈ (Finset.Icc 2 n).erase p :=
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨le_refl 2, hn⟩⟩
      have hterm : ∀ i ∈ (Finset.Icc 2 n).erase p,
          0 ≤ padicValRat p (((i : ℚ)))⁻¹ := by
        intro j hj
        have hjI := Finset.mem_of_mem_erase hj
        have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hjI).1
        have hjn : j ≤ n := (Finset.mem_Icc.mp hjI).2
        have hjp : j ≠ p := Finset.ne_of_mem_erase hj
        have hndvd : ¬ p ∣ j := by
          intro hdvd
          obtain ⟨mm, rfl⟩ := hdvd
          have hmm0 : mm ≠ 0 := by
            rintro rfl
            omega
          have hmm1 : mm ≠ 1 := by
            rintro rfl
            simp at hjp
          have hmm2 : 2 ≤ mm := by omega
          have hle2 : 2 * p ≤ p * mm := by
            calc 2 * p = p * 2 := by ring
            _ ≤ p * mm := Nat.mul_le_mul_left p hmm2
          omega
        have h0 : padicValNat p j = 0 := padicValNat.eq_zero_of_not_dvd hndvd
        simp [padicValRat.inv, padicValRat.of_nat, h0]
      have hRest : 0 ≤ padicValRat p
          (∑ j ∈ (Finset.Icc 2 n).erase p, ((j : ℚ))⁻¹) :=
        padicValRat_nonneg_of_sum_nonneg hterm
      have hR'pos : 0 < ∑ j ∈ (Finset.Icc 2 n).erase p, ((j : ℚ))⁻¹ := by
        refine Finset.sum_pos (fun i hi => ?_) ⟨2, h2mem⟩
        have hi2 : 2 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
        have hpos : (0 : ℚ) < ((i : ℚ)) := by
          have hi0 : 0 < i := by omega
          exact_mod_cast hi0
        exact inv_pos.mpr hpos
      have hR'ne := ne_of_gt hR'pos
      have hpcast : ((p : ℚ)) ≠ 0 := by exact_mod_cast hpP.ne_zero
      have hqne : ((p : ℚ))⁻¹ ≠ 0 := inv_ne_zero hpcast
      have hRne : ((p : ℚ))⁻¹ + ∑ j ∈ (Finset.Icc 2 n).erase p, ((j : ℚ))⁻¹ ≠ 0 := by
        rw [← hsplit, ← hB]
        exact hH1
      have hltval : padicValRat p (((p : ℚ)))⁻¹
          < padicValRat p (∑ j ∈ (Finset.Icc 2 n).erase p, ((j : ℚ))⁻¹) := by
        rw [hFp]
        omega
      have hRp : padicValRat p (harmonic n - 1) = -1 := by
        rw [hB, hsplit, padicValRat.add_eq_of_lt hRne hqne hR'ne hltval]
        exact hFp
      have hndvd : ¬ p ∣ n + 1 := by
        intro hdvd
        rw [hm] at hdvd
        have h2 : p ∣ 2 := hpP.dvd_of_dvd_pow hdvd
        have h12 := (Nat.dvd_prime Nat.prime_two).mp h2
        rcases h12 with rfl | rfl
        · exact absurd rfl hpP.ne_one
        · omega
      have h0 : padicValNat p (n + 1) = 0 := padicValNat.eq_zero_of_not_dvd hndvd
      have hn1v : padicValRat p ((((n + 1 : ℕ))) : ℚ) = 0 := by
        rw [padicValRat.of_nat, h0, Nat.cast_zero]
      have hvalSp : padicValRat p ((((n + 1 : ℕ)) : ℚ) * (harmonic n - 1)) = -1 := by
        rw [padicValRat.mul hcast hH1, hn1v, hRp, zero_add]
      have hnormp : 1 < padicNorm p ((((n + 1 : ℕ)) : ℚ) * (harmonic n - 1)) := by
        rw [padicNorm.eq_zpow_of_nonzero hSne, hvalSp, neg_neg, zpow_one]
        exact_mod_cast hpP.one_lt
      intro hcon
      obtain ⟨kk, hkk⟩ := hcon
      have hcastI : ((kk : ℤ) : ℚ).isInt = true := by
        simp [Rat.isInt, Rat.den_intCast]
      rw [hkk] at hcastI
      exact (padicNorm.not_int_of_not_padic_int p hnormp) hcastI
  · -- Otherwise the `2`-adic valuation of the sum is negative.
    have htk : padicValNat 2 (n + 1) < Nat.log 2 n := by
      by_contra hc
      have hkt : Nat.log 2 n ≤ padicValNat 2 (n + 1) := not_lt.mp hc
      have h2k : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
      have hnk : n < 2 ^ (Nat.log 2 n + 1) := by
        have hlt2 := Nat.lt_pow_succ_log_self one_lt_two n
        rwa [Nat.succ_eq_add_one] at hlt2
      have hdvd : 2 ^ Nat.log 2 n ∣ n + 1 :=
        (pow_dvd_pow 2 hkt).trans pow_padicValNat_dvd
      obtain ⟨m', hm'⟩ := hdvd
      have hXpos : 0 < 2 ^ Nat.log 2 n := by positivity
      have hm'0 : m' ≠ 0 := by
        rintro rfl
        omega
      have hm'1 : m' ≠ 1 := by
        rintro rfl
        simp at hm'
        omega
      have hm'2 : m' = 2 := by
        have hlo : 1 < m' := by omega
        have hhi : m' ≤ 2 := by
          have h2k1 : 2 ^ (Nat.log 2 n + 1) = 2 ^ Nat.log 2 n * 2 := pow_succ 2 _
          have hle : 2 ^ Nat.log 2 n * m' ≤ 2 ^ Nat.log 2 n * 2 := by omega
          exact Nat.le_of_mul_le_mul_left hle hXpos
        omega
      subst hm'2
      exact hpow ⟨Nat.log 2 n + 1, hm'.trans (pow_succ 2 (Nat.log 2 n)).symm⟩
    have hnorm : 1 < padicNorm 2 ((((n + 1 : ℕ)) : ℚ) * (harmonic n - 1)) := by
      rw [padicNorm.eq_zpow_of_nonzero hSne, hvalS]
      have hexp : -((((padicValNat 2 (n + 1) : ℕ)) : ℤ)
          + -((((Nat.log 2 n : ℕ))) : ℤ))
          = ((((Nat.log 2 n - padicValNat 2 (n + 1) : ℕ))) : ℤ) := by
        rw [Nat.cast_sub htk.le]
        ring
      rw [hexp, zpow_natCast]
      exact one_lt_pow₀ one_lt_two
        (by omega : Nat.log 2 n - padicValNat 2 (n + 1) ≠ 0)
    intro hcon
    obtain ⟨kk, hkk⟩ := hcon
    have hcastI : ((kk : ℤ) : ℚ).isInt = true := by
      simp [Rat.isInt, Rat.den_intCast]
    rw [hkk] at hcastI
    exact (padicNorm.not_int_of_not_padic_int 2 hnorm) hcastI

end

end MetaMathlibExt
