/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.GCDMonoid.FinsetLemmas

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

-- Step 0: the three filters are pairwise disjoint; union is S.
private theorem rhs_merge (n : ℕ) :
    Finset.prod
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ ¬ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum))
      (fun p => p) *
    Finset.prod
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum))
      (fun p => p) *
    Finset.prod
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ (Nat.digits p (n + 1)).sum < p))
      (fun p => p) =
    Finset.prod
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ (p ∣ (n + 1) ∨ p ≤ (Nat.digits p (n + 1)).sum)))
      (fun p => p) := by
  have hAB : Disjoint
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ ¬ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum))
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum)) := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact h1.2.1 h2.2.1
  have hABC : Disjoint
      (((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ ¬ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum)) ∪
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum)))
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ (Nat.digits p (n + 1)).sum < p)) := by
    rw [Finset.disjoint_union_left]
    constructor <;>
    · rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega
  have hunion :
      (((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ ¬ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum)) ∪
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum)) ∪
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ (Nat.digits p (n + 1)).sum < p))) =
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ (p ∣ (n + 1) ∨ p ≤ (Nat.digits p (n + 1)).sum))) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ((⟨hr, hp, _, hle⟩ | ⟨hr, hp, hdvd, _⟩) | ⟨hr, hp, hdvd, _⟩)
      · exact ⟨hr, hp, Or.inr hle⟩
      · exact ⟨hr, hp, Or.inl hdvd⟩
      · exact ⟨hr, hp, Or.inl hdvd⟩
    · rintro ⟨hr, hp, h⟩
      by_cases hdvd : p ∣ (n + 1)
      · by_cases hle : p ≤ (Nat.digits p (n + 1)).sum
        · exact Or.inl (Or.inr ⟨hr, hp, hdvd, hle⟩)
        · exact Or.inr ⟨hr, hp, hdvd, by omega⟩
      · refine Or.inl (Or.inl ⟨hr, hp, hdvd, ?_⟩)
        cases h with
        | inl h' => exact absurd h' hdvd
        | inr h' => exact h'
  rw [← hunion, Finset.prod_union hABC, Finset.prod_union hAB]

-- Kummer consequence: q prime, q ∤ C(n,k) → digit sums satisfy s_q(k) ≤ s_q(n).
private theorem kummer_digit_le {q k n : ℕ} (hq : Nat.Prime q) (hkn : k ≤ n)
    (hdiv : ¬ q ∣ n.choose k) : (q.digits k).sum ≤ (q.digits n).sum := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hpos : 0 < n.choose k := Nat.choose_pos hkn
  have hval : padicValNat q (n.choose k) = 0 := by
    rw [padicValNat.eq_zero_iff]
    right; right
    exact hdiv
  have hkum := sub_one_mul_padicValNat_choose_eq_sub_sum_digits hkn (p := q)
  rw [hval, mul_zero] at hkum
  omega

-- Coefficient form: every support index i satisfies i ≤ n.
private theorem support_le {n i : ℕ} (hi : i ∈ (Polynomial.bernoulli n).support) : i ≤ n := by
  by_contra h
  push Not at h
  have hcoeff : (Polynomial.bernoulli n).coeff i = 0 := by
    rw [Polynomial.coeff_bernoulli]
    simp [Nat.not_le.mpr h]
  exact (Polynomial.mem_support_iff.mp hi) hcoeff

-- Positivity of digit sums.
private theorem digit_sum_pos {b m : ℕ} (hb : 1 < b) (hm : 0 < m) : 0 < (b.digits m).sum := by
  have hne : b.digits m ≠ [] := by
    intro hz
    have hlen := Nat.length_digits b m hb (by omega)
    rw [hz] at hlen
    simp at hlen
  have hlast := List.getLast_mem hne
  have hne0 : (b.digits m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero b (by omega)
  have hle := List.le_sum_of_mem hlast
  omega

-- If (q-1) | k with k ≥ 1 then s_q(k) ≥ q-1 (multiple + positive).
private theorem digit_sum_ge_of_dvd {q k : ℕ} (hq : Nat.Prime q) (hk1 : 1 ≤ k)
    (hdvd : q - 1 ∣ k) : q - 1 ≤ (q.digits k).sum := by
  rcases eq_or_ne q 2 with rfl | hne2
  · have hle := digit_sum_pos (show (1:ℕ) < 2 by norm_num) (show 0 < k by omega)
    omega
  · have hq3 : 3 ≤ q := by
      have h2 := hq.two_le
      omega
    have hmod1 : q % (q - 1) = 1 := by
      have hqq : q = (q - 1) + 1 := by omega
      nth_rewrite 1 [hqq]
      rw [Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    have hme := Nat.modEq_digits_sum (q - 1) q hmod1 k
    have hk0 : k ≡ 0 [MOD q - 1] := Nat.modEq_zero_iff_dvd.mpr hdvd
    have hs0 : (q.digits k).sum ≡ 0 [MOD q - 1] := hme.symm.trans hk0
    have hdvd2 : q - 1 ∣ (q.digits k).sum := Nat.modEq_zero_iff_dvd.mp hs0
    have hpos : 0 < (q.digits k).sum :=
      digit_sum_pos hq.one_lt (show 0 < k by omega)
    exact Nat.le_of_dvd hpos hdvd2

-- Kummer + divisibility: q ∈ T₀ (i.e. (q-1)|k, ¬ q|C(n,k)) gives s_q(n) ≥ q-1.
private theorem digit_sum_n_ge_of_mem {q k n : ℕ} (hq : Nat.Prime q) (hkn : k ≤ n)
    (hk1 : 1 ≤ k) (hdvd : q - 1 ∣ k) (hdiv : ¬ q ∣ n.choose k) :
    q - 1 ≤ (q.digits n).sum := by
  have h1 : q - 1 ≤ (q.digits k).sum := digit_sum_ge_of_dvd hq hk1 hdvd
  have h2 : (q.digits k).sum ≤ (q.digits n).sum := by
    have : Fact (Nat.Prime q) := ⟨hq⟩
    have hpos : 0 < n.choose k := Nat.choose_pos hkn
    have hval : padicValNat q (n.choose k) = 0 := by
      rw [padicValNat.eq_zero_iff]
      right; right
      exact hdiv
    have hkum := sub_one_mul_padicValNat_choose_eq_sub_sum_digits hkn (p := q)
    rw [hval, mul_zero] at hkum
    omega
  omega

private theorem digit_sum_succ_of_not_dvd {q n : ℕ} (hq : Nat.Prime q) (h : ¬ q ∣ (n + 1)) :
    (q.digits (n + 1)).sum = (q.digits n).sum + 1 := by
  have hq1 : 1 < q := hq.one_lt
  have hmod : (n + 1) % q ≠ 0 := fun hz => h (Nat.dvd_of_mod_eq_zero hz)
  have hQ : (n + 1) / q = n / q := Nat.succ_div_of_mod_ne_zero hmod
  have hlt : n % q + 1 < q := by
    by_contra hc
    simp only [Nat.not_lt] at hc
    have h1 : n % q < q := Nat.mod_lt _ (by omega)
    have heq : n % q + 1 = q := by omega
    have h2 : (n + 1) % q = (n % q + 1 % q) % q := Nat.add_mod n 1 q
    rw [Nat.mod_eq_of_lt hq1, heq, Nat.mod_self] at h2
    exact hmod h2
  have hmodval : (n + 1) % q = n % q + 1 := by
    have h2 : (n + 1) % q = (n % q + 1 % q) % q := Nat.add_mod n 1 q
    rw [Nat.mod_eq_of_lt hq1, Nat.mod_eq_of_lt hlt] at h2
    exact h2
  have e1 : q.digits (n + 1) = ((n + 1) % q) :: q.digits ((n + 1) / q) :=
    Nat.digits_def' hq1 (Nat.succ_pos n)
  by_cases hn : n = 0
  · subst hn
    have d1 : q.digits 1 = [1] := by
      have e := Nat.digits_def' hq1 (show (0:ℕ) < 1 by norm_num)
      have m1 : (1:ℕ) % q = 1 := Nat.mod_eq_of_lt hq1
      have q1 : (1:ℕ) / q = 0 := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [m1, q1, Nat.digits_zero] at e
      exact e
    change (q.digits (0 + 1)).sum = (q.digits 0).sum + 1
    rw [show (0:ℕ) + 1 = 1 from rfl, d1, Nat.digits_zero]
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have e2 : q.digits n = (n % q) :: q.digits (n / q) := Nat.digits_def' hq1 hnpos
    rw [e1, e2, hQ, hmodval, List.sum_cons, List.sum_cons]
    omega

private theorem digit_ge_of_dvd_succ {q n : ℕ} (hq : Nat.Prime q) (h : q ∣ (n + 1)) :
    q - 1 ≤ (q.digits n).sum := by
  have hq1 : 1 < q := hq.one_lt
  have hmod : (n + 1) % q = 0 := Nat.mod_eq_zero_of_dvd h
  have hn : n ≠ 0 := by
    rintro rfl
    simp only [zero_add, Nat.dvd_one] at h
    exact absurd h (by omega)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have h1 : n % q < q := Nat.mod_lt _ (by omega)
  have hdigit : n % q = q - 1 := by
    have h2 : (n + 1) % q = (n % q + 1 % q) % q := Nat.add_mod n 1 q
    rw [Nat.mod_eq_of_lt hq1] at h2
    have h4 : (n % q + 1) % q = 0 := h2.symm.trans hmod
    have h3 : n % q + 1 = q := by
      by_cases hc : n % q + 1 < q
      · rw [Nat.mod_eq_of_lt hc] at h4
        omega
      · simp only [Nat.not_lt] at hc
        omega
    omega
  have e2 : q.digits n = (n % q) :: q.digits (n / q) := Nat.digits_def' hq1 hnpos
  rw [e2, hdigit, List.sum_cons]
  exact Nat.le_add_right _ _

private theorem factF {q n : ℕ} (hq : Nat.Prime q) :
    q - 1 ≤ (q.digits n).sum ↔ (q ∣ (n + 1) ∨ q ≤ (q.digits (n + 1)).sum) := by
  constructor
  · intro hge
    by_cases hdvd : q ∣ (n + 1)
    · exact Or.inl hdvd
    · right
      have := digit_sum_succ_of_not_dvd hq hdvd
      omega
  · rintro (hdvd | hle)
    · exact digit_ge_of_dvd_succ hq hdvd
    · by_cases hdvd : q ∣ (n + 1)
      · exact digit_ge_of_dvd_succ hq hdvd
      · have := digit_sum_succ_of_not_dvd hq hdvd
        omega

-- Binary digit sum of an odd m ≥ 3 is at least 2.
private theorem two_le_digit_sum_of_odd {m : ℕ} (hodd : Odd m) (hm : 3 ≤ m) :
    2 ≤ (Nat.digits 2 m).sum := by
  have h1 : (1:ℕ) < 2 := by norm_num
  have hpos : 0 < m := by omega
  have hmod : m % 2 = 1 := Nat.odd_iff.mp hodd
  have hdiv : m / 2 ≠ 0 := by omega
  have e : Nat.digits 2 m = (m % 2) :: Nat.digits 2 (m / 2) := Nat.digits_def' h1 hpos
  rw [e, hmod, List.sum_cons]
  have hne : Nat.digits 2 (m / 2) ≠ [] := by
    intro hz
    have hlen := Nat.length_digits 2 (m / 2) h1 hdiv
    rw [hz] at hlen
    simp at hlen
  have hlast := List.getLast_mem hne
  have hne0 : (Nat.digits 2 (m / 2)).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 2 hdiv
  have hle := List.le_sum_of_mem hlast
  omega

-- 2 is always in S for n ≥ 1.
private theorem two_mem_S {n : ℕ} (hn : 1 ≤ n) :
    2 ∈ (Finset.range (n + 2)).filter
      (fun p => Nat.Prime p ∧ (p ∣ (n + 1) ∨ p ≤ (Nat.digits p (n + 1)).sum)) := by
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, Nat.prime_two, ?_⟩
  by_cases hdvd : 2 ∣ (n + 1)
  · exact Or.inl hdvd
  · right
    have hodd : Odd (n + 1) := by
      rw [Nat.odd_iff]
      have h1 : (n + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have h2 : (n + 1) % 2 ≠ 0 := fun hz => hdvd (Nat.dvd_of_mod_eq_zero hz)
      omega
    have hm3 : 3 ≤ n + 1 := by omega
    have := two_le_digit_sum_of_odd hodd hm3
    simpa using this

-- Upper bound, k = 0 case: den = 1.
private theorem upper_k_zero {n : ℕ} (k : ℕ) (hk : k = 0) (S : Finset ℕ) :
    (bernoulli k * (n.choose k : ℚ)).den ∣ ∏ p ∈ S, p := by
  subst hk
  simp only [bernoulli_zero, one_mul]
  rw [Rat.den_natCast]
  exact one_dvd _

-- Upper bound, odd k ≠ 1 case: bernoulli k = 0, den = 1.
private theorem upper_k_odd {n k : ℕ} (hodd : Odd k) (hne1 : k ≠ 1) (S : Finset ℕ) :
    (bernoulli k * (n.choose k : ℚ)).den ∣ ∏ p ∈ S, p := by
  have h1 : 1 < k := by
    by_contra hc
    simp only [Nat.not_lt] at hc
    interval_cases k
    · simp at hodd
    · exact absurd rfl hne1
  have hB : bernoulli k = 0 := bernoulli_eq_zero_of_odd hodd h1
  rw [hB, zero_mul, Rat.den_zero]
  exact one_dvd _

-- Upper bound, k = 1 case: den divides 2 and 2 ∈ S.
private theorem upper_k_one {n : ℕ} (hn : 1 ≤ n) :
    (bernoulli 1 * (n.choose 1 : ℚ)).den ∣
    ∏ p ∈ (Finset.range (n + 2)).filter
      (fun p => Nat.Prime p ∧ (p ∣ (n + 1) ∨ p ≤ (Nat.digits p (n + 1)).sum)), p := by
  rw [bernoulli_one, Nat.choose_one_right]
  have hd : ((-1 / 2 : ℚ)).den = 2 := by norm_num
  have h2 : ((-1 / 2 : ℚ) * (n : ℚ)).den ∣ ((-1 / 2 : ℚ)).den * ((n : ℚ)).den :=
    Rat.mul_den_dvd _ _
  rw [hd, Rat.den_natCast, mul_one] at h2
  exact dvd_trans h2 (Finset.dvd_prod_of_mem _ (two_mem_S hn))

-- Upper bound, even k ≥ 2 case via von Staudt–Clausen.
private theorem upper_k_even {n k : ℕ} (hkn : k ≤ n) (h2 : 2 ≤ k) (heven : Even k) :
    (bernoulli k * (n.choose k : ℚ)).den ∣
    ∏ p ∈ (Finset.range (n + 2)).filter
      (fun p => Nat.Prime p ∧ (p ∣ (n + 1) ∨ p ≤ (Nat.digits p (n + 1)).sum)), p := by
  obtain ⟨m, hm⟩ := heven
  have hkm : k = 2 * m := by omega
  subst hkm
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
  have hB : bernoulli (2 * m) =
      (z : ℚ) - ∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m), (1 : ℚ) / (p : ℚ) := by
    have hz' : (z : ℚ) = bernoulli (2 * m) +
        ∑ p ∈ (Finset.range (2 * m + 2)).filter
          (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m), (1 : ℚ) / (p : ℚ) := hz
    rw [eq_sub_iff_add_eq]
    exact hz'.symm
  have hterm : ∀ p ∈ (Finset.range (2 * m + 2)).filter
      (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
      (fun p => p ∣ n.choose (2 * m)),
      (n.choose (2 * m) : ℚ) / (p : ℚ) = ((n.choose (2 * m) / p : ℕ) : ℚ) := by
    intro p hp
    have hpc : p ∣ n.choose (2 * m) := (Finset.mem_filter.mp hp).2
    have hpT := (Finset.mem_filter.mp hp).1
    have hmem := Finset.mem_filter.mp hpT
    have hprime : Nat.Prime p := hmem.2.1
    have hne : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hprime.ne_zero
    exact (Nat.cast_div hpc hne).symm
  have hT1_int : ∑ p ∈ (Finset.range (2 * m + 2)).filter
      (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
      (fun p => p ∣ n.choose (2 * m)),
      (n.choose (2 * m) : ℚ) / (p : ℚ) =
      (((∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => p ∣ n.choose (2 * m)), n.choose (2 * m) / p : ℕ)) : ℚ) := by
    calc ∑ p ∈ (Finset.range (2 * m + 2)).filter
          (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
          (fun p => p ∣ n.choose (2 * m)),
          (n.choose (2 * m) : ℚ) / (p : ℚ)
        = ∑ p ∈ (Finset.range (2 * m + 2)).filter
          (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
          (fun p => p ∣ n.choose (2 * m)), ((n.choose (2 * m) / p : ℕ) : ℚ) :=
        Finset.sum_congr rfl hterm
      _ = (((∑ p ∈ (Finset.range (2 * m + 2)).filter
          (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
          (fun p => p ∣ n.choose (2 * m)), n.choose (2 * m) / p : ℕ)) : ℚ) :=
        (Nat.cast_sum _ _).symm
  have hsplit : ∑ p ∈ (Finset.range (2 * m + 2)).filter
      (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m), (n.choose (2 * m) : ℚ) / (p : ℚ) =
      (∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => p ∣ n.choose (2 * m)), (n.choose (2 * m) : ℚ) / (p : ℚ)) +
      (∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => ¬ p ∣ n.choose (2 * m)), (n.choose (2 * m) : ℚ) / (p : ℚ)) :=
    (Finset.sum_filter_add_sum_filter_not _ (fun p => p ∣ n.choose (2 * m)) _).symm
  have hsum_eq : ∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m),
        ((1 : ℚ) / (p : ℚ)) * (n.choose (2 * m) : ℚ) =
      ∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m),
        (n.choose (2 * m) : ℚ) / (p : ℚ) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [div_mul_eq_mul_div, one_mul]
  have hT1_Q : ∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => p ∣ n.choose (2 * m)),
        (n.choose (2 * m) : ℚ) / (p : ℚ) =
      ∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => p ∣ n.choose (2 * m)), ((n.choose (2 * m) / p : ℕ) : ℚ) :=
    Finset.sum_congr rfl hterm
  have wdef : ∃ w : ℤ, bernoulli (2 * m) * (n.choose (2 * m) : ℚ) =
      (w : ℚ) - ∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => ¬ p ∣ n.choose (2 * m)), (n.choose (2 * m) : ℚ) / (p : ℚ) := by
    refine ⟨(n.choose (2 * m) : ℤ) * z -
      ∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => p ∣ n.choose (2 * m)), ((n.choose (2 * m) / p : ℕ) : ℤ), ?_⟩
    have hwQ : ((((n.choose (2 * m) : ℤ) * z -
        ∑ p ∈ (Finset.range (2 * m + 2)).filter
          (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
          (fun p => p ∣ n.choose (2 * m)), ((n.choose (2 * m) / p : ℕ) : ℤ)) : ℤ) : ℚ) =
        (n.choose (2 * m) : ℚ) * (z : ℚ) -
        ∑ p ∈ (Finset.range (2 * m + 2)).filter
          (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
          (fun p => p ∣ n.choose (2 * m)), ((n.choose (2 * m) / p : ℕ) : ℚ) := by
      have h1 : ((((n.choose (2 * m) : ℤ) * z -
          ∑ p ∈ (Finset.range (2 * m + 2)).filter
            (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
            (fun p => p ∣ n.choose (2 * m)), ((n.choose (2 * m) / p : ℕ) : ℤ)) : ℤ) : ℚ) =
          ((((n.choose (2 * m) : ℤ) * z : ℤ)) : ℚ) -
          ((((∑ p ∈ (Finset.range (2 * m + 2)).filter
            (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
            (fun p => p ∣ n.choose (2 * m)), ((n.choose (2 * m) / p : ℕ) : ℤ)) : ℤ)) : ℚ) :=
        Int.cast_sub _ _
      have h2 : ((((n.choose (2 * m) : ℤ) * z : ℤ)) : ℚ) =
          (n.choose (2 * m) : ℚ) * (z : ℚ) := by simp
      have h3 : ((((∑ p ∈ (Finset.range (2 * m + 2)).filter
            (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
            (fun p => p ∣ n.choose (2 * m)), ((n.choose (2 * m) / p : ℕ) : ℤ)) : ℤ)) : ℚ) =
          ∑ p ∈ (Finset.range (2 * m + 2)).filter
            (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
            (fun p => p ∣ n.choose (2 * m)), ((n.choose (2 * m) / p : ℕ) : ℚ) := by
        simp only [Int.cast_sum]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        exact Int.cast_natCast _
      rw [h1, h2, h3]
    rw [hwQ, hB, sub_mul, Finset.sum_mul, hsum_eq, hsplit, hT1_Q,
      sub_add_eq_sub_sub]
    have eA : (↑z * (n.choose (2 * m) : ℚ)) = ((n.choose (2 * m) : ℚ) * ↑z) :=
      mul_comm _ _
    rw [eA]
  obtain ⟨w, hw⟩ := wdef
  have hden0 : (bernoulli (2 * m) * (n.choose (2 * m) : ℚ)).den =
      (∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => ¬ p ∣ n.choose (2 * m)),
        (n.choose (2 * m) : ℚ) / (p : ℚ)).den := by
    rw [hw, Rat.intCast_sub_den]
  rw [hden0]
  have hstep1 : (∑ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => ¬ p ∣ n.choose (2 * m)),
        (n.choose (2 * m) : ℚ) / (p : ℚ)).den ∣
      ∏ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => ¬ p ∣ n.choose (2 * m)), p := by
    apply dvd_trans (Finset.Rat.den_sum_dvd_prod_den _ _)
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    have hpT := (Finset.mem_filter.mp hp).1
    have hmem := Finset.mem_filter.mp hpT
    have hprime : Nat.Prime p := hmem.2.1
    have hpos : 0 < p := hprime.pos
    have h := Rat.mul_den_dvd (n.choose (2 * m) : ℚ) ((p : ℚ)⁻¹)
    rw [Rat.den_natCast, Rat.inv_natCast_den_of_pos hpos, one_mul] at h
    rw [div_eq_mul_inv]
    exact h
  have hstep2 : ∏ p ∈ (Finset.range (2 * m + 2)).filter
        (fun p => Nat.Prime p ∧ p - 1 ∣ 2 * m) |>.filter
        (fun p => ¬ p ∣ n.choose (2 * m)), p ∣
      ∏ p ∈ (Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ (p ∣ (n + 1) ∨ p ≤ (Nat.digits p (n + 1)).sum)), p := by
    apply Finset.prod_dvd_prod_of_subset
    intro q hq
    have hq0 := Finset.mem_filter.mp hq
    have hqT := hq0.1
    have hnc : ¬ q ∣ n.choose (2 * m) := hq0.2
    have hTm := Finset.mem_filter.mp hqT
    have hqr := hTm.1
    have hprime := hTm.2.1
    have hdiv := hTm.2.2
    have hqr' : q < n + 2 := by
      rw [Finset.mem_range] at hqr
      omega
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hqr', hprime, ?_⟩
    exact (factF hprime).mp
      (digit_sum_n_ge_of_mem hprime hkn (by omega) hdiv hnc)
  exact dvd_trans hstep1 hstep2

-- Small digit sums: s_p(x) = x for x < p.
private theorem digit_sum_small {p x : ℕ} (hp : 1 < p) (hx : x < p) :
    (p.digits x).sum = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Nat.digits_zero, List.sum_nil]
  · have hpos : 0 < x := Nat.pos_of_ne_zero hx0
    have e := Nat.digits_def' hp hpos
    rw [Nat.mod_eq_of_lt hx, Nat.div_eq_of_lt hx, Nat.digits_zero] at e
    rw [e, List.sum_cons, List.sum_nil, add_zero]

-- Digit sum of r + p*q splits.
private theorem digit_sum_add {p r q : ℕ} (hp : 1 < p) (hr : r < p) :
    (p.digits (r + p * q)).sum = r + (p.digits q).sum := by
  by_cases h0 : r = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp
  · have hne : r ≠ 0 ∨ q ≠ 0 := by
      by_cases h : r = 0
      · exact Or.inr (fun hz => h0 ⟨h, hz⟩)
      · exact Or.inl h
    have e := Nat.digits_add p hp r q hr hne
    rw [e, List.sum_cons]

-- No-borrow sub-number: for every t ≤ s_p(n) there is k ≤ n with s_p(k) = t
-- and s_p(n-k) = s_p(n) - t.
private theorem exists_digit_subnumber {p : ℕ} (hp : 1 < p) (n : ℕ) :
    ∀ t, t ≤ (p.digits n).sum →
    ∃ k, k ≤ n ∧ (p.digits k).sum = t ∧
      (p.digits (n - k)).sum = (p.digits n).sum - t := by
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro t ht
  rcases eq_or_ne n 0 with rfl | hn0
  · have ht0 : t = 0 := by
      simp only [Nat.digits_zero, List.sum_nil, Nat.le_zero] at ht
      exact ht
    refine ⟨0, le_rfl, by simp [Nat.digits_zero, ht0], by simp [Nat.digits_zero, ht0]⟩
  · have hp0 : 0 < p := by omega
    have hr : n % p < p := Nat.mod_lt _ hp0
    have hdecomp : n % p + p * (n / p) = n := Nat.mod_add_div n p
    have hrq : n % p ≠ 0 ∨ n / p ≠ 0 := by
      by_cases h : n % p = 0
      · by_cases h2 : n / p = 0
        · exfalso
          apply hn0
          rw [h, h2, mul_zero, add_zero] at hdecomp
          exact hdecomp.symm
        · exact Or.inr h2
      · exact Or.inl h
    have hsum : (p.digits n).sum = n % p + (p.digits (n / p)).sum := by
      have e : p.digits (n % p + p * (n / p)) = (n % p) :: p.digits (n / p) :=
        Nat.digits_add p hp _ _ hr hrq
      rw [hdecomp] at e
      rw [e, List.sum_cons]
    by_cases htr : t ≤ n % p
    · refine ⟨t, le_trans htr (Nat.mod_le n p), ?_, ?_⟩
      · exact digit_sum_small hp (lt_of_le_of_lt htr hr)
      · have e : n - t = (n % p - t) + p * (n / p) := by omega
        have h1 : (p.digits (n - t)).sum =
            (n % p - t) + (p.digits (n / p)).sum := by
          rw [e]
          exact digit_sum_add hp (by omega)
        rw [h1]
        omega
    · have hrt : n % p < t := by omega
      have ht'S : t - n % p ≤ (p.digits (n / p)).sum := by omega
      have hqn : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hp
      obtain ⟨k', hk'q, hsk', hsd'⟩ := ih (n / p) hqn (t - n % p) ht'S
      refine ⟨n % p + p * k', ?_, ?_, ?_⟩
      · have hmul : p * k' ≤ p * (n / p) := Nat.mul_le_mul le_rfl hk'q
        have hkle : n % p + p * k' ≤ n := by omega
        exact hkle
      · have e : (p.digits (n % p + p * k')).sum =
            n % p + (p.digits k').sum := digit_sum_add hp hr
        rw [e, hsk']
        omega
      · have hmul : p * k' ≤ p * (n / p) := Nat.mul_le_mul le_rfl hk'q
        have e1 : n - (n % p + p * k') = p * (n / p) - p * k' := by omega
        have e2 : p * (n / p) - p * k' = p * (n / p - k') :=
          (Nat.mul_sub p _ _).symm
        have hnk : n - (n % p + p * k') = 0 + p * (n / p - k') := by
          rw [e1, e2, zero_add]
        have hsd_nk : (p.digits (n - (n % p + p * k'))).sum =
            (p.digits (n / p - k')).sum := by
          rw [hnk, digit_sum_add hp (show (0:ℕ) < p by omega), zero_add]
        rw [hsd_nk, hsd']
        omega

-- Even Bernoulli denominator divisibility.
private theorem even_den_dvd {k p : ℕ} (hprime : Nat.Prime p) (heven : Even k) (hk2 : 2 ≤ k)
    (hdvd : p - 1 ∣ k) : p ∣ (bernoulli k).den := by
  have : Fact (Nat.Prime p) := ⟨hprime⟩
  obtain ⟨m, hm⟩ := heven
  have h2m : k = 2 * m := by omega
  have hm0 : 0 < m := by omega
  have hdvd2 : p - 1 ∣ 2 * m := by
    rw [← h2m]
    exact hdvd
  rw [h2m]
  exact Bernoulli.dvd_den_bernoulli hm0 hdvd2

-- Lower bound core: every p ∈ S divides the support-lcm.
private theorem lower_mem_S {n p : ℕ}
    (hp : p ∈ (Finset.range (n + 2)).filter
      (fun p => Nat.Prime p ∧ (p ∣ (n + 1) ∨ p ≤ (Nat.digits p (n + 1)).sum))) :
    p ∣ (Polynomial.bernoulli n).support.lcm
      (fun i => ((Polynomial.bernoulli n).coeff i).den) := by
  rw [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hprange, hprime, hmem⟩ := hp
  have hp2 : 2 ≤ p := hprime.two_le
  have hge : p - 1 ≤ (p.digits n).sum := (factF hprime).mpr hmem
  obtain ⟨k, hkn, hsk, hsd⟩ :=
    exists_digit_subnumber hprime.one_lt n (p - 1) hge
  have hk1 : 1 ≤ k := by
    by_contra hc
    have hk0 : k = 0 := by omega
    rw [hk0, Nat.digits_zero, List.sum_nil] at hsk
    omega
  have hnc : ¬ p ∣ n.choose k := by
    have : Fact (Nat.Prime p) := ⟨hprime⟩
    have hpos : 0 < n.choose k := Nat.choose_pos hkn
    have hkum := sub_one_mul_padicValNat_choose_eq_sub_sum_digits hkn (p := p)
    have hrhs : (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum = 0 := by
      omega
    rw [hrhs] at hkum
    have hv0 : padicValNat p (n.choose k) = 0 := by
      rcases Nat.mul_eq_zero.mp hkum with h | h
      · omega
      · exact h
    rw [padicValNat.eq_zero_iff] at hv0
    rcases hv0 with h | h | h
    · exact absurd h hprime.ne_one
    · omega
    · exact h
  have hdvd_k : p - 1 ∣ k := by
    rcases eq_or_ne p 2 with rfl | hne
    · exact one_dvd k
    · have hp3 : 3 ≤ p := by
        have h2 := hprime.two_le
        omega
      have hmod1 : p % (p - 1) = 1 := by
        have hqq : p = (p - 1) + 1 := by omega
        nth_rewrite 1 [hqq]
        rw [Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      have hme := Nat.modEq_digits_sum (p - 1) p hmod1 k
      rw [hsk] at hme
      have hz : p - 1 ≡ 0 [MOD p - 1] := Nat.modEq_zero_iff_dvd.mpr dvd_rfl
      exact Nat.modEq_zero_iff_dvd.mp (hme.trans hz)
  have hden : p ∣ (bernoulli k).den := by
    rcases eq_or_ne p 2 with rfl | hne_p2
    · by_cases hk1_eq : k = 1
      · subst hk1_eq
        rw [bernoulli_one]
        have hd : ((-1 / 2 : ℚ)).den = 2 := by norm_num
        rw [hd]
      · have heven_k : Even k := by
          have hsk1 : (Nat.digits 2 k).sum = 1 := by omega
          have hne1 : k % 2 ≠ 1 := by
            intro hmod
            have hdecomp := Nat.mod_add_div k 2
            have hsum2 : (Nat.digits 2 (k % 2 + 2 * (k / 2))).sum =
                k % 2 + (Nat.digits 2 (k / 2)).sum :=
              digit_sum_add (by norm_num) (Nat.mod_lt _ (by norm_num))
            rw [hdecomp] at hsum2
            rw [hmod] at hsum2
            have hq0 : k / 2 = 0 := by
              by_contra hc
              have hpos : 0 < k / 2 := Nat.pos_of_ne_zero hc
              have hpos2 := digit_sum_pos (show (1:ℕ) < 2 by norm_num) hpos
              omega
            have hk1eq : k = 1 := by omega
            exact hk1_eq hk1eq
          have hmod0 : k % 2 = 0 := by
            have hlt : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
            omega
          exact Nat.even_iff.mpr hmod0
        have hk2 : 2 ≤ k := by
          rcases heven_k with ⟨m, hm⟩
          omega
        exact even_den_dvd hprime heven_k hk2 hdvd_k
    · have heven_k : Even k := by
        have hodd_p : Odd p := hprime.odd_of_ne_two hne_p2
        have heven_sub : Even (p - 1) := by
          obtain ⟨j, hj⟩ := hodd_p
          exact ⟨j, by omega⟩
        obtain ⟨a, ha⟩ := heven_sub
        obtain ⟨b, hb⟩ := hdvd_k
        exact ⟨a * b, by rw [hb, ha]; ring⟩
      have hk2 : 2 ≤ k := by
        rcases heven_k with ⟨m, hm⟩
        omega
      exact even_den_dvd hprime heven_k hk2 hdvd_k
  have hcpos : 0 < n.choose k := Nat.choose_pos hkn
  have hne_c : ((n.choose k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hcpos
  have hB_eq : bernoulli k =
      (bernoulli k * (n.choose k : ℚ)) * (((n.choose k : ℕ) : ℚ))⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ hne_c, mul_one]
  have hden_dvd : (bernoulli k).den ∣
      (bernoulli k * (n.choose k : ℚ)).den * n.choose k := by
    have h := Rat.mul_den_dvd (bernoulli k * (n.choose k : ℚ))
      ((((n.choose k : ℕ) : ℚ))⁻¹)
    rw [← hB_eq, Rat.inv_natCast_den_of_pos hcpos] at h
    exact h
  have hp_den : p ∣ (bernoulli k * (n.choose k : ℚ)).den := by
    rcases hprime.dvd_mul.mp (dvd_trans hden hden_dvd) with h | h
    · exact h
    · exact absurd h hnc
  have hkj : n - (n - k) = k := Nat.sub_sub_self hkn
  have hcoeff_j : (Polynomial.bernoulli n).coeff (n - k) =
      bernoulli k * ((n.choose k : ℕ) : ℚ) := by
    have hle : n - k ≤ n := Nat.sub_le n k
    rw [Polynomial.coeff_bernoulli, ite_eq_left hle, hkj, Nat.choose_symm hkn]
  have hmem_supp : n - k ∈ (Polynomial.bernoulli n).support := by
    rw [Polynomial.mem_support_iff, hcoeff_j]
    intro hz
    rw [hz, Rat.den_zero] at hp_den
    have hle1 : p ≤ 1 := Nat.le_of_dvd (by norm_num) hp_den
    omega
  have hmem2 : ((Polynomial.bernoulli n).coeff (n - k)).den ∣
      (Polynomial.bernoulli n).support.lcm
        (fun i => ((Polynomial.bernoulli n).coeff i).den) :=
    Finset.dvd_lcm hmem_supp
  rw [hcoeff_j] at hmem2
  exact dvd_trans hp_den hmem2

/-- **Kellner–Sondow factorization of the denominators of Bernoulli polynomials.** Let $B_k$
denote the $k$-th Bernoulli number, with $B_1 = -1/2$, let
$B_n(x) = \sum_{k=0}^{n} \binom{n}{k} B_k x^{n-k}$ be the $n$-th Bernoulli polynomial, and let
$D_n$ be the least common multiple of the denominators of its nonzero coefficients. For a prime
$p$, let $s_p(N)$ denote the sum of the base-$p$ digits of a natural number $N$. Then for every
$n \ge 1$, $D_n$ is the product of three factors: the product of the primes $p \le n + 1$ with
$p \nmid n + 1$ and $s_p(n+1) \ge p$; the product of the primes $p \le n + 1$ with $p \mid n + 1$
and $s_p(n+1) \ge p$; and the product of the primes $p \le n + 1$ with $p \mid n + 1$ and
$s_p(n+1) < p$.

Proves `Wanted` entry `kellner_sondow_bernoulli_denom`.

Source: Bernd C. Kellner, "On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients," Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem
`thm:triple`, lines 351–358, <https://cs.uwaterloo.ca/journals/JIS/VOL27/Kellner/kell2.tex>,
restating B. C. Kellner and J. Sondow, "On Carmichael and polygonal numbers, Bernoulli polynomials,
and sums of base-p digits," Integers 21 (2021), Theorem 3.1. Factor definitions `eq:ddprod2` at
lines 341–346.
-/
theorem kellner_sondow_bernoulli_denom : ∀ (n : ℕ), 1 ≤ n →
  (Polynomial.bernoulli n).support.lcm (fun i => ((Polynomial.bernoulli n).coeff i).den) =
    Finset.prod
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ ¬ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum))
      (fun p => p) *
    Finset.prod
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum))
      (fun p => p) *
    Finset.prod
      ((Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ (Nat.digits p (n + 1)).sum < p))
      (fun p => p) := by
  intro n hn
  rw [rhs_merge n]
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro i hi
    have hle : i ≤ n := support_le hi
    have hcoeff : (Polynomial.bernoulli n).coeff i =
        bernoulli (n - i) * ((n.choose (n - i) : ℕ) : ℚ) := by
      rw [Polynomial.coeff_bernoulli, ite_eq_left hle]
      have hkk : n - i ≤ n := Nat.sub_le n i
      have hCi : ((n.choose i : ℕ) : ℚ) = ((n.choose (n - i) : ℕ) : ℚ) := by
        have hsym : n.choose i = n.choose (n - i) := by
          have hsub : n - (n - i) = i := Nat.sub_sub_self hle
          conv_lhs => rw [← hsub]
          exact Nat.choose_symm hkk
        rw [hsym]
      rw [hCi]
    rw [hcoeff]
    by_cases hk0 : n - i = 0
    · exact upper_k_zero (n - i) hk0 _
    · by_cases hk1 : n - i = 1
      · rw [hk1]
        exact upper_k_one hn
      · rcases Nat.even_or_odd (n - i) with hev | hod
        · have h2 : 2 ≤ n - i := by omega
          have hkn' : n - i ≤ n := Nat.sub_le n i
          exact upper_k_even hkn' h2 hev
        · exact upper_k_odd hod hk1 _
  · apply Finset.prod_primes_dvd
    · intro a ha
      rw [Finset.mem_filter] at ha
      exact ha.2.1.prime
    · intro a ha
      exact lower_mem_S ha

end MetaMathlibExt
end
