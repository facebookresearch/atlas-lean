/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CollatzArithmeticDerivative
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

/-!
# Bounds on the factors of compatible semiprimes

Suppose the semiprimes `p * q` and `r * s` are compatible, where `q < p`. Then `241 ≤ r`,
`241 ≤ s`, `3 * q < r < 3 * p` and `3 * q < s < 3 * p`
(`IsCompatibleSemiprimePair.bounds`).

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Lemma 11
(`jis-2025-25.1.8-lem-11`).
-/

namespace MetaMathlibExt

@[expose] public section

namespace IsCompatibleSemiprimePair

private def checkDiv (p m : ℕ) : Bool :=
  decide (p ≤ m) || !decide (m ∣ p)

private def treeAll (c : ℕ → Bool) : ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool)
    (fun lo hi => if hi ≤ lo then true else false)
    (fun _fuel ih lo hi =>
      if hi ≤ lo + 1 then (if hi ≤ lo then true else c lo)
      else ih lo (lo + (hi - lo) / 2) && ih (lo + (hi - lo) / 2) hi)

private theorem treeAll_zero (c : ℕ → Bool) (lo hi : ℕ) :
    treeAll c 0 lo hi = (if hi ≤ lo then true else false) := rfl

private theorem treeAll_succ (c : ℕ → Bool) (fuel lo hi : ℕ) :
    treeAll c (fuel + 1) lo hi =
      (if hi ≤ lo + 1 then (if hi ≤ lo then true else c lo)
       else treeAll c fuel lo (lo + (hi - lo) / 2) &&
         treeAll c fuel (lo + (hi - lo) / 2) hi) := rfl

private theorem treeAll_all (c : ℕ → Bool) (fuel : ℕ) : ∀ (lo hi : ℕ),
    treeAll c fuel lo hi = true → ∀ (m : ℕ), lo ≤ m → m < hi → c m = true := by
  induction fuel with
  | zero =>
    intro lo hi h m hmlo hmhi
    rw [treeAll_zero] at h
    by_cases hlo : hi ≤ lo
    · exfalso; omega
    · simp [hlo] at h
  | succ fuel ih =>
    intro lo hi h m hmlo hmhi
    rw [treeAll_succ] at h
    by_cases hle : hi ≤ lo + 1
    · simp only [hle, ite_true] at h
      by_cases hlo : hi ≤ lo
      · exfalso; omega
      · simp only [hlo, ite_false] at h
        have hmeq : m = lo := by omega
        rw [hmeq]
        exact h
    · simp only [hle, ite_false] at h
      rw [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      by_cases hmid : m < lo + (hi - lo) / 2
      · exact ih lo (lo + (hi - lo) / 2) h1 m hmlo hmid
      · exact ih (lo + (hi - lo) / 2) hi h2 m (by omega) hmhi

private theorem treeAll_of_all (c : ℕ → Bool) (fuel : ℕ) : ∀ (lo hi : ℕ),
    (∀ m, lo ≤ m → m < hi → c m = true) → hi - lo ≤ fuel →
    treeAll c fuel lo hi = true := by
  induction fuel with
  | zero =>
    intro lo hi H hsize
    rw [treeAll_zero]
    have hle : hi ≤ lo := by omega
    simp [hle]
  | succ fuel ih =>
    intro lo hi H hsize
    rw [treeAll_succ]
    by_cases hle : hi ≤ lo + 1
    · simp only [hle, ite_true]
      by_cases hlo : hi ≤ lo
      · simp [hlo]
      · simp only [hlo, ite_false]
        exact H lo le_rfl (by omega)
    · simp only [hle, ite_false]
      rw [Bool.and_eq_true]
      constructor
      · apply ih
        · intro m hm1 hm2
          exact H m hm1 (by omega)
        · omega
      · apply ih
        · intro m hm1 hm2
          exact H m (by omega) hm2
        · omega

private def primeCheck (p : ℕ) : Bool :=
  decide (2 ≤ p) && treeAll (checkDiv p) 309 2 311

private theorem checkDiv_eq_true {p m : ℕ} (hprime : p.Prime) (hm2 : 2 ≤ m) :
    checkDiv p m = true := by
  simp only [checkDiv]
  by_cases hle : p ≤ m
  · simp [hle]
  · have hxdvd : ¬ m ∣ p := by
      intro hdvd
      rcases hprime.eq_one_or_self_of_dvd m hdvd with rfl | heq
      · omega
      · omega
    simp [hle, hxdvd]

private theorem not_dvd_of_checkDiv {p m : ℕ} (h : checkDiv p m = true)
    (hnm : ¬ p ≤ m) : ¬ m ∣ p := by
  have hdec : decide (p ≤ m) = false := by simp [hnm]
  simp only [checkDiv, hdec, Bool.false_or] at h
  simpa using h

private theorem primeCheck_eq_true {p : ℕ} (hp : p ≤ 96100) :
    primeCheck p = true ↔ p.Prime := by
  have hsqrt310 : p.sqrt ≤ 310 := by
    by_contra hcon
    have h311 : 311 ≤ p.sqrt := by omega
    have hle := Nat.le_sqrt.mp h311
    omega
  constructor
  · intro hcheck
    simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨hp2, hloop⟩ := hcheck
    rw [Nat.prime_def_le_sqrt]
    refine ⟨hp2, fun m hm2 hmsqrt hmdvd => ?_⟩
    have hlt : p.sqrt < p := Nat.sqrt_lt_self (by omega)
    have hnm : ¬ p ≤ m := by omega
    have hcm : checkDiv p m = true :=
      treeAll_all (checkDiv p) 309 2 311 hloop m hm2 (by omega)
    exact absurd hmdvd (not_dvd_of_checkDiv hcm hnm)
  · intro hprime
    simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hprime.two_le, ?_⟩
    apply treeAll_of_all
    · intro m hm2 _
      exact checkDiv_eq_true hprime hm2
    · omega

private def checkPair (q d : ℕ) : Bool :=
  !(decide (3 ≤ q) && decide (1 ≤ d) && decide (d ≤ 239 - 3 * q) &&
    decide (2 * d ∣ 15 * q ^ 2 + 1) && primeCheck q) ||
  !(primeCheck (3 * q + d) && primeCheck (3 * q + (15 * q ^ 2 + 1) / (2 * d)) &&
    primeCheck (11 * q + 2 * d + 2 * ((15 * q ^ 2 + 1) / (2 * d))))

private theorem bounds_check :
    treeAll (fun q => treeAll (checkPair q) 240 0 240) 80 0 80 = true := by decide

private theorem mul_three_lt_of_compatible {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) (hqp : q < p) : 3 * q < r ∧ 3 * q < s := by
  obtain ⟨hp, hq, hr, hs, hsum, hprod⟩ := h
  have hsum' : 2 * ((r : ℤ) + (s : ℤ)) = (p : ℤ) + (q : ℤ) := by exact_mod_cast hsum
  have hprod' : 2 * ((r : ℤ) * (s : ℤ)) = 3 * ((p : ℤ) * (q : ℤ)) + 1 := by exact_mod_cast hprod
  have huv : 2 * (((r : ℤ) - 3 * (q : ℤ)) * ((s : ℤ) - 3 * (q : ℤ))) =
      15 * (q : ℤ) ^ 2 + 1 := by
    linear_combination hprod' - 3 * (q : ℤ) * hsum'
  have huvpos : (0 : ℤ) < ((r : ℤ) - 3 * (q : ℤ)) * ((s : ℤ) - 3 * (q : ℤ)) := by
    have h := sq_nonneg ((q : ℤ))
    linarith
  rcases mul_pos_iff.mp huvpos with ⟨hr3, hs3⟩ | ⟨hr3, hs3⟩
  · refine ⟨by omega, by omega⟩
  · exfalso
    have hr3' : (r : ℤ) ≤ 3 * (q : ℤ) - 1 := by omega
    have hs3' : (s : ℤ) ≤ 3 * (q : ℤ) - 1 := by omega
    have hrs_le : (r : ℤ) * (s : ℤ) ≤ (3 * (q : ℤ) - 1) * (3 * (q : ℤ) - 1) :=
      mul_le_mul hr3' hs3' (by exact_mod_cast Nat.zero_le s)
        (by have h2 := hq.two_le; omega)
    have hq2' : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.two_le
    have h3pq : 3 * (p : ℤ) * (q : ℤ) ≤ (18 * (q : ℤ) - 11) * (q : ℤ) := by
      linarith [hprod', hrs_le]
    have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq.pos
    have h3p : 3 * (p : ℤ) ≤ 18 * (q : ℤ) - 11 :=
      (mul_le_mul_iff_of_pos_right hqpos).mp h3pq
    have hsq := sq_nonneg ((r : ℤ) - (s : ℤ))
    have hkey : (0 : ℤ) ≤ ((p : ℤ) + (q : ℤ)) ^ 2 - 24 * (p : ℤ) * (q : ℤ) - 8 := by
      have hrr : ((p : ℤ) + (q : ℤ)) ^ 2 - 24 * (p : ℤ) * (q : ℤ) - 8 =
          4 * (((r : ℤ) - (s : ℤ)) ^ 2) := by
        linear_combination 8 * hprod' -
          (((p : ℤ) + (q : ℤ)) + 2 * ((r : ℤ) + (s : ℤ))) * hsum'
      linarith
    have h21 : 21 * (q : ℤ) + 1 ≤ (p : ℤ) := by
      by_contra hcon
      have hle : (p : ℤ) ≤ 21 * (q : ℤ) := by omega
      have h1 : (0 : ℤ) ≤ (21 * (q : ℤ) - (p : ℤ)) * (p : ℤ) :=
        mul_nonneg (by omega) (by exact_mod_cast Nat.zero_le p)
      have hpq1 : (1 : ℤ) ≤ (p : ℤ) - (q : ℤ) := by
        have hqp' : (q : ℤ) < (p : ℤ) := by exact_mod_cast hqp
        omega
      have h2 : (0 : ℤ) ≤ ((q : ℤ) - 2) * ((p : ℤ) - (q : ℤ)) :=
        mul_nonneg (by omega) (by omega)
      linarith [hkey, h1, h2]
    linarith [h3p, h21]

private theorem ge_241_of_compatible {p q r s : ℕ} (h : IsCompatibleSemiprimePair p q r s)
    (h3r : 3 * q < r) (h3s : 3 * q < s) : 241 ≤ r := by
  obtain ⟨hp, hq, hr, hs, hsum, hprod⟩ := h
  by_contra hcon
  have hr239 : r ≤ 239 := by
    have h240 : r ≤ 240 := by omega
    rcases eq_or_ne r 240 with rfl | hne
    · norm_num at hr
    · omega
  have hq3 : 3 ≤ q := by
    have h2 := hq.two_le
    by_contra hqcon
    have hq2 : q = 2 := by omega
    rw [hq2] at hprod
    omega
  have hq79 : q ≤ 79 := by omega
  obtain ⟨d, hrd⟩ : ∃ d, r = 3 * q + d := ⟨r - 3 * q, by omega⟩
  obtain ⟨e, hse⟩ : ∃ e, s = 3 * q + e := ⟨s - 3 * q, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have he1 : 1 ≤ e := by omega
  have hd239 : d ≤ 239 - 3 * q := by omega
  have hde : 2 * d * e = 15 * q ^ 2 + 1 := by
    have hsum' : 2 * ((r : ℤ) + (s : ℤ)) = (p : ℤ) + (q : ℤ) := by exact_mod_cast hsum
    have hprod' : 2 * ((r : ℤ) * (s : ℤ)) = 3 * ((p : ℤ) * (q : ℤ)) + 1 := by exact_mod_cast hprod
    have hd' : (d : ℤ) = (r : ℤ) - 3 * (q : ℤ) := by omega
    have he' : (e : ℤ) = (s : ℤ) - 3 * (q : ℤ) := by omega
    have huv : 2 * (d : ℤ) * (e : ℤ) = 15 * (q : ℤ) ^ 2 + 1 := by
      rw [hd', he']
      linear_combination hprod' - 3 * (q : ℤ) * hsum'
    exact_mod_cast huv
  have hpe : p = 11 * q + 2 * d + 2 * e := by omega
  have hdiv : 2 * d ∣ 15 * q ^ 2 + 1 := ⟨e, hde.symm⟩
  have hq2 : q ^ 2 ≤ 6241 := by
    have h : q * q ≤ 79 * 79 := mul_le_mul hq79 hq79 (Nat.zero_le _) (Nat.zero_le _)
    rw [Nat.pow_two]
    omega
  have h2e : 2 * e ≤ 15 * q ^ 2 + 1 := by
    have hXe : e ≤ d * e := Nat.le_mul_of_pos_left e (show 0 < d by omega)
    have hde2 : 2 * (d * e) = 15 * q ^ 2 + 1 := by rw [← mul_assoc]; exact hde
    omega
  have hsB : s ≤ 96100 := by omega
  have hpB : p ≤ 96100 := by omega
  have hrB : r ≤ 96100 := by omega
  have hqB : q ≤ 96100 := by omega
  have he_eq : e = (15 * q ^ 2 + 1) / (2 * d) := by
    conv_rhs => rw [← hde]
    exact (Nat.mul_div_cancel_left e (show 0 < 2 * d by omega)).symm
  have hseq : s = 3 * q + (15 * q ^ 2 + 1) / (2 * d) := by rw [hse, he_eq]
  have hpeq : p = 11 * q + 2 * d + 2 * ((15 * q ^ 2 + 1) / (2 * d)) := by rw [hpe, he_eq]
  have key : checkPair q d = true → False := by
    intro hall2
    have hc1 : decide (3 ≤ q) = true := by simp [hq3]
    have hc2 : decide (1 ≤ d) = true := by simp [hd1]
    have hc3 : decide (d ≤ 239 - 3 * q) = true := by simp [hd239]
    have hc4 : decide (2 * d ∣ 15 * q ^ 2 + 1) = true := by simp [hdiv]
    have hcq : primeCheck q = true := (primeCheck_eq_true hqB).mpr hq
    have hcr : primeCheck r = true := (primeCheck_eq_true hrB).mpr hr
    have hcs : primeCheck s = true := (primeCheck_eq_true hsB).mpr hs
    have hcp : primeCheck p = true := (primeCheck_eq_true hpB).mpr hp
    rw [hrd] at hcr
    rw [hseq] at hcs
    rw [hpeq] at hcp
    simp [checkPair, hc1, hc2, hc3, hc4, hcq, hcr, hcs, hcp] at hall2
  have hq80 : q < 80 := by omega
  have hd240 : d < 240 := by omega
  have hinner : treeAll (checkPair q) 240 0 240 = true :=
    treeAll_all _ 80 0 80 bounds_check q (Nat.zero_le q) hq80
  have hqd : checkPair q d = true :=
    treeAll_all _ 240 0 240 hinner d (Nat.zero_le d) hd240
  exact key hqd

/-- **Bounds on the factors of compatible semiprimes.** Suppose the semiprimes $pq$ and $rs$ are
compatible, where $q < p$. Then $r \ge 241$, $s \ge 241$, $3q < r < 3p$ and $3q < s < 3p$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Lemma 11
(`jis-2025-25.1.8-lem-11`). -/
theorem bounds {p q r s : ℕ} (h : IsCompatibleSemiprimePair p q r s) (hqp : q < p) :
    241 ≤ r ∧ 241 ≤ s ∧ 3 * q < r ∧ 3 * q < s ∧ r < 3 * p ∧ s < 3 * p := by
  obtain ⟨hp, hq, hr, hs, hsum, hprod⟩ := h
  obtain ⟨h3r, h3s⟩ := mul_three_lt_of_compatible ⟨hp, hq, hr, hs, hsum, hprod⟩ hqp
  have hs2 := hs.two_le
  have hr2 := hr.two_le
  have hp2 := hp.two_le
  have hr3p : r < 3 * p := by omega
  have hs3p : s < 3 * p := by omega
  have hr241 : 241 ≤ r :=
    ge_241_of_compatible ⟨hp, hq, hr, hs, hsum, hprod⟩ h3r h3s
  have hsymm : IsCompatibleSemiprimePair p q s r :=
    ⟨hp, hq, hs, hr, by omega, by linear_combination hprod⟩
  have hs241 : 241 ≤ s := ge_241_of_compatible hsymm h3s h3r
  exact ⟨hr241, hs241, h3r, h3s, hr3p, hs3p⟩

end IsCompatibleSemiprimePair

end

end MetaMathlibExt
