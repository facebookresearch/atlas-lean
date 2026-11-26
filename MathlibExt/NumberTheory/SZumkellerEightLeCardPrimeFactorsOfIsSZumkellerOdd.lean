/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.SumSquaredDivisorsProduct
public import MathlibExt.NumberTheory.SZumkeller

/-!
# Odd s-Zumkeller numbers divisible by three

Every odd s-Zumkeller number divisible by `3` has at least eight distinct prime
factors. This is Proposition 6(ii) of Jayanta Kalita and Helen K. Saikia's
*A Study on Generalized Zumkeller Numbers*.
-/

namespace MetaMathlibExt

/-- The map `x ↦ x ^ 2 / (x ^ 2 - 1)` is antitone on integers `≥ 2`. -/
private theorem sq_div_sub_one_le_of_le {x y : ℕ} (hx : 2 ≤ x)
    (hxy : x ≤ y) :
    (y : ℚ) ^ 2 / (y ^ 2 - 1) ≤ (x : ℚ) ^ 2 / (x ^ 2 - 1) := by
  have hx2 : (2 : ℚ) ≤ x := by exact_mod_cast hx
  have hy2 : (2 : ℚ) ≤ y := by exact_mod_cast hx.trans hxy
  have hdx : (0 : ℚ) < (x : ℚ) ^ 2 - 1 := by
    have h : (1 : ℚ) < (x : ℚ) ^ 2 := one_lt_pow₀ (by linarith) (by norm_num)
    linarith
  have hdy : (0 : ℚ) < (y : ℚ) ^ 2 - 1 := by
    have h : (1 : ℚ) < (y : ℚ) ^ 2 := one_lt_pow₀ (by linarith) (by norm_num)
    linarith
  rw [div_le_div_iff₀ hdy hdx]
  have hxy' : (x : ℚ) ≤ (y : ℚ) := by exact_mod_cast hxy
  have hnn := mul_nonneg (sub_nonneg.mpr hxy')
    (show (0 : ℚ) ≤ (x : ℚ) + (y : ℚ) by positivity)
  have hsq : (x : ℚ) ^ 2 ≤ (y : ℚ) ^ 2 := by linarith [hnn]
  linarith [hsq]

/-- The values `x ^ 2 / (x ^ 2 - 1)` are positive for integers `x ≥ 2`. -/
private theorem sq_div_sub_one_pos {x : ℕ} (hx : 2 ≤ x) :
    (0 : ℚ) < (x : ℚ) ^ 2 / (x ^ 2 - 1) := by
  have hx0 : (0 : ℚ) < x := by exact_mod_cast (by omega : 0 < x)
  have h2 : (1 : ℚ) < (x : ℚ) ^ 2 :=
    one_lt_pow₀ (by exact_mod_cast (by omega : 1 < x)) (by norm_num)
  exact div_pos (pow_pos hx0 2) (by linarith)

/-- An odd prime outside `{3, 5, 7, 11, 13, 17, 19}` is at least `23`. -/
private theorem twentythree_le_of_prime_of_not_mem {q : ℕ} (hq : q.Prime)
    (hodd : Odd q)
    (hmem : q ∉ ({3, 5, 7, 11, 13, 17, 19} : Finset ℕ)) :
    23 ≤ q := by
  have h2 := hq.two_le
  have hne : q ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hodd
    norm_num at hodd
  have h3 : 3 ≤ q := by omega
  by_contra hlt
  push Not at hlt
  have hall : ∀ r ∈ Finset.Ico 3 23, r.Prime → r % 2 = 1 →
      r ∈ ({3, 5, 7, 11, 13, 17, 19} : Finset ℕ) := by decide
  exact hmem (hall q (Finset.mem_Ico.mpr ⟨h3, hlt⟩) hq (Nat.odd_iff.mp hodd))

/-- A product over at most seven odd primes is maximized at
`{3, 5, 7, 11, 13, 17, 19}`. -/
private theorem prod_le_prod_small_primes (s : Finset ℕ)
    (hsprime : ∀ p ∈ s, p.Prime) (hsodd : ∀ p ∈ s, Odd p)
    (hcard : s.card ≤ 7) :
    ∏ p ∈ s, (p : ℚ) ^ 2 / (p ^ 2 - 1) ≤
      ∏ p ∈ ({3, 5, 7, 11, 13, 17, 19} : Finset ℕ),
        (p : ℚ) ^ 2 / (p ^ 2 - 1) := by
  set v : Finset ℕ := {3, 5, 7, 11, 13, 17, 19} with hv
  have hvcard : v.card = 7 := by rw [hv]; decide
  have hunion : ∀ a b : Finset ℕ, a \ b ∪ a ∩ b = a := by
    intro a b
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdisj : ∀ a b : Finset ℕ, Disjoint (a \ b) (a ∩ b) := by
    intro a b
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hx1 hx2
    tauto
  have e1 : (s \ v).card + (s ∩ v).card = s.card := by
    have h := congrArg Finset.card (hunion s v)
    rwa [Finset.card_union_of_disjoint (hdisj s v)] at h
  have e2 : (v \ s).card + (v ∩ s).card = v.card := by
    have h := congrArg Finset.card (hunion v s)
    rwa [Finset.card_union_of_disjoint (hdisj v s)] at h
  have e3 : (s ∩ v).card = (v ∩ s).card := by rw [Finset.inter_comm]
  have hcarddiff : (s \ v).card ≤ (v \ s).card := by omega
  have hleft : ∏ q ∈ s \ v, (q : ℚ) ^ 2 / (q ^ 2 - 1) ≤
      ((23 : ℚ) ^ 2 / ((23 : ℚ) ^ 2 - 1)) ^ (s \ v).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod₀
    · intro q hq
      have hqs : q ∈ s := (Finset.mem_sdiff.mp hq).1
      exact le_of_lt (sq_div_sub_one_pos ((hsprime q hqs).two_le))
    · intro q hq
      have hqs : q ∈ s := (Finset.mem_sdiff.mp hq).1
      have hqv : q ∉ v := (Finset.mem_sdiff.mp hq).2
      have hqv' : q ∉ ({3, 5, 7, 11, 13, 17, 19} : Finset ℕ) := by
        rwa [hv] at hqv
      have h23 : 23 ≤ q :=
        twentythree_le_of_prime_of_not_mem (hsprime q hqs) (hsodd q hqs) hqv'
      exact sq_div_sub_one_le_of_le (by norm_num) h23
  have hC1 : (1 : ℚ) ≤ (23 : ℚ) ^ 2 / ((23 : ℚ) ^ 2 - 1) := by norm_num
  have hpow : ((23 : ℚ) ^ 2 / ((23 : ℚ) ^ 2 - 1)) ^ (s \ v).card ≤
      ((23 : ℚ) ^ 2 / ((23 : ℚ) ^ 2 - 1)) ^ (v \ s).card :=
    pow_le_pow_right₀ hC1 hcarddiff
  have hright : ((23 : ℚ) ^ 2 / ((23 : ℚ) ^ 2 - 1)) ^ (v \ s).card ≤
      ∏ r ∈ v \ s, (r : ℚ) ^ 2 / (r ^ 2 - 1) := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod₀
    · intro r _
      exact le_of_lt (by norm_num : (0 : ℚ) < (23 : ℚ) ^ 2 / ((23 : ℚ) ^ 2 - 1))
    · intro r hr
      have hrv : r ∈ v := (Finset.mem_sdiff.mp hr).1
      rw [hv] at hrv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrv
      have hboth : 2 ≤ r ∧ r ≤ 23 := by
        rcases hrv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
      exact sq_div_sub_one_le_of_le hboth.1 hboth.2
  have hkey : ∏ q ∈ s \ v, (q : ℚ) ^ 2 / (q ^ 2 - 1) ≤
      ∏ r ∈ v \ s, (r : ℚ) ^ 2 / (r ^ 2 - 1) :=
    hleft.trans (hpow.trans hright)
  have hA0 : (0 : ℚ) ≤ ∏ p ∈ s ∩ v, (p : ℚ) ^ 2 / (p ^ 2 - 1) := by
    apply Finset.prod_nonneg
    intro p hp
    have hps : p ∈ s := (Finset.mem_inter.mp hp).1
    exact le_of_lt (sq_div_sub_one_pos ((hsprime p hps).two_le))
  have hdecomp_s : ∏ p ∈ s, (p : ℚ) ^ 2 / (p ^ 2 - 1) =
      (∏ p ∈ s ∩ v, (p : ℚ) ^ 2 / (p ^ 2 - 1)) *
        ∏ q ∈ s \ v, (q : ℚ) ^ 2 / (q ^ 2 - 1) := by
    have h := Finset.prod_union (f := fun p : ℕ => (p : ℚ) ^ 2 / (p ^ 2 - 1))
      (hdisj s v)
    rw [hunion s v] at h
    rw [h, mul_comm]
  have hdecomp_v : ∏ p ∈ v, (p : ℚ) ^ 2 / (p ^ 2 - 1) =
      (∏ p ∈ s ∩ v, (p : ℚ) ^ 2 / (p ^ 2 - 1)) *
        ∏ r ∈ v \ s, (r : ℚ) ^ 2 / (r ^ 2 - 1) := by
    have h := Finset.prod_union (f := fun p : ℕ => (p : ℚ) ^ 2 / (p ^ 2 - 1))
      (hdisj v s)
    rw [hunion v s, Finset.inter_comm v s] at h
    rw [h, mul_comm]
  rw [hdecomp_s, hdecomp_v]
  exact mul_le_mul_of_nonneg_left hkey hA0

/-- For an s-Zumkeller number `n ≠ 1`, `1 + 2 / minFac ^ 2 ≤ σ₂(n) / n ^ 2`. -/
private theorem one_add_le_sigma_div (n : ℕ) (h : IsSZumkeller n)
    (hn1 : n ≠ 1) :
    1 + 2 / (n.minFac : ℚ) ^ 2 ≤ (ArithmeticFunction.sigma 2 n : ℚ) / n ^ 2 := by
  obtain ⟨A, hA, hneA, -, hbal⟩ := h
  have hn01 : 1 < n := Nat.nonempty_properDivisors.mp (hneA.mono hA)
  have hn0 : n ≠ 0 := by omega
  have hprime := Nat.minFac_prime hn1
  have hpdvd := Nat.minFac_dvd n
  have hp2 : 2 ≤ n.minFac := hprime.two_le
  have hmmem : n / n.minFac ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors]
    refine ⟨Nat.div_dvd_of_dvd hpdvd,
      Nat.div_lt_self (by omega) (by omega : 1 < n.minFac)⟩
  have hle : (n / n.minFac) ^ 2 ≤ ∑ d ∈ A, d ^ 2 := by
    by_cases hmA : n / n.minFac ∈ A
    · exact Finset.single_le_sum (f := fun d : ℕ => d ^ 2)
        (fun d _ => Nat.zero_le _) hmA
    · have hmem : n / n.minFac ∈ n.properDivisors \ A :=
        Finset.mem_sdiff.mpr ⟨hmmem, hmA⟩
      have h := Finset.single_le_sum (f := fun d : ℕ => d ^ 2)
        (fun d _ => Nat.zero_le _) hmem
      rwa [← hbal] at h
  have hσ : ArithmeticFunction.sigma 2 n
      = n ^ 2 + ∑ d ∈ n.properDivisors, d ^ 2 := by
    rw [ArithmeticFunction.sigma_apply, ← Nat.insert_self_properDivisors hn0,
      Finset.sum_insert Nat.self_notMem_properDivisors]
  have hsplit := Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hA
  have hnat : n ^ 2 + 2 * (n / n.minFac) ^ 2 ≤
      ArithmeticFunction.sigma 2 n := by
    omega
  have hcast : (n : ℚ) ^ 2 + 2 * ((n / n.minFac : ℕ) : ℚ) ^ 2 ≤
      ArithmeticFunction.sigma 2 n := by
    exact_mod_cast hnat
  have hn0' : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2pos : (0 : ℚ) < (n : ℚ) ^ 2 := pow_pos hn0' 2
  have hn2ne : (n : ℚ) ^ 2 ≠ 0 := (pow_pos hn0' 2).ne'
  have hp0' : (0 : ℚ) < n.minFac := by exact_mod_cast (by omega : 0 < n.minFac)
  have hp2ne : (n.minFac : ℚ) ^ 2 ≠ 0 := (pow_pos hp0' 2).ne'
  have hmp : ((n / n.minFac : ℕ) : ℚ) * n.minFac = n := by
    exact_mod_cast Nat.div_mul_cancel hpdvd
  have hmp2 : ((n / n.minFac : ℕ) : ℚ) ^ 2 * (n.minFac : ℚ) ^ 2
      = (n : ℚ) ^ 2 := by
    have h := congrArg (fun x : ℚ => x ^ 2) hmp
    simpa [mul_pow] using h
  have hsq : ((n / n.minFac : ℕ) : ℚ) ^ 2 / (n : ℚ) ^ 2
      = 1 / (n.minFac : ℚ) ^ 2 := by
    rw [div_eq_div_iff hn2ne hp2ne, one_mul]
    exact hmp2
  have hcancel : 2 * (((n / n.minFac : ℕ) : ℚ) ^ 2 / (n : ℚ) ^ 2) * (n : ℚ) ^ 2
      = 2 * ((n / n.minFac : ℕ) : ℚ) ^ 2 := by
    rw [mul_assoc, div_mul_cancel₀ _ hn2ne]
  have h2split : (2 : ℚ) / (n.minFac : ℚ) ^ 2 = 2 * (1 / (n.minFac : ℚ) ^ 2) :=
    (mul_one_div 2 _).symm
  have hstep : (1 : ℚ) + 2 / (n.minFac : ℚ) ^ 2
      = ((n : ℚ) ^ 2 + 2 * ((n / n.minFac : ℕ) : ℚ) ^ 2) / (n : ℚ) ^ 2 := by
    rw [h2split, ← hsq, eq_div_iff hn2ne, add_mul, one_mul, hcancel]
  calc (1 : ℚ) + 2 / (n.minFac : ℚ) ^ 2
      = ((n : ℚ) ^ 2 + 2 * ((n / n.minFac : ℕ) : ℚ) ^ 2) / (n : ℚ) ^ 2 := hstep
    _ ≤ (ArithmeticFunction.sigma 2 n : ℚ) / (n : ℚ) ^ 2 :=
        (div_le_div_iff_of_pos_right hn2pos).mpr hcast

/-- **Odd s-Zumkeller numbers divisible by $3$ have at least eight prime factors.** Every odd
s-Zumkeller number divisible by $3$ has at least $8$ distinct prime factors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 6(ii). -/
public theorem eight_le_card_primeFactors_of_isSZumkeller_odd (n : ℕ)
    (h : IsSZumkeller n) (ho : Odd n) (h3 : 3 ∣ n) : 8 ≤ n.primeFactors.card := by
  have hn01 : 1 < n := by
    obtain ⟨A, hA, hneA, -, -⟩ := h
    exact Nat.nonempty_properDivisors.mp (hneA.mono hA)
  have hn1 : n ≠ 1 := by omega
  have hn0 : n ≠ 0 := by omega
  have hminfac : n.minFac = 3 := by
    have hprime := Nat.minFac_prime hn1
    have hle : n.minFac ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) h3
    have hodd : Odd n.minFac := by
      rcases hprime.eq_two_or_odd with h2eq | hmod
      · exfalso
        have hdvd2 : 2 ∣ n := by
          rw [← h2eq]
          exact Nat.minFac_dvd n
        have heven : Even n := even_iff_two_dvd.mpr hdvd2
        rw [Nat.even_iff] at heven
        rw [Nat.odd_iff] at ho
        omega
      · exact Nat.odd_iff.mpr hmod
    have hge : 3 ≤ n.minFac := by
      have h2 := hprime.two_le
      obtain ⟨k, hk⟩ := hodd
      omega
    omega
  have hsodd : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rcases hpp.eq_two_or_odd with h2eq | hmod
    · exfalso
      have hdvd2 : 2 ∣ n := by
        rw [← h2eq]
        exact Nat.dvd_of_mem_primeFactors hp
      have heven : Even n := even_iff_two_dvd.mpr hdvd2
      rw [Nat.even_iff] at heven
      rw [Nat.odd_iff] at ho
      omega
    · exact Nat.odd_iff.mpr hmod
  have hup := (sigma_two_prod_formulas n hn0).2.2 hn01
  have hlow := one_add_le_sigma_div n h hn1
  rw [hminfac] at hlow
  norm_num at hlow
  by_contra hlt
  push Not at hlt
  have hcomp := prod_le_prod_small_primes n.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hsodd
    (by omega : n.primeFactors.card ≤ 7)
  have hnum : ∏ p ∈ ({3, 5, 7, 11, 13, 17, 19} : Finset ℕ),
      (p : ℚ) ^ 2 / (p ^ 2 - 1) < 11 / 9 := by
    decide +kernel
  linarith [hup, hcomp, hnum]

end MetaMathlibExt
