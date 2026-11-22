/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Squarefree

@[expose] public section

namespace MetaMathlibExt

section
private def stormU (a : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => 2 * a * stormU a (n + 1) - stormU a n
private theorem stormU_succ2 (a : ℤ) (k : ℕ) :
    stormU a (k + 2) = 2 * a * stormU a (k + 1) - stormU a k := by
  cases k with
  | zero => simp [stormU]
  | succ k => simp [stormU]

private theorem stormU_two (a : ℤ) : stormU a 2 = 2 * a := by simp [stormU]
private theorem stormU_three (a : ℤ) : stormU a 3 = 4 * a ^ 2 - 1 := by simp [stormU]; ring

private theorem stormU_twostep (a : ℤ) (k : ℕ) :
    stormU a (k + 4) = (4 * a ^ 2 - 2) * stormU a (k + 2) - stormU a k := by
  have h1 := stormU_succ2 a (k + 2)
  have h2 := stormU_succ2 a (k + 1)
  have h3 := stormU_succ2 a k
  have e1 : k + 2 + 2 = k + 4 := by omega
  have e2 : k + 2 + 1 = k + 3 := by omega
  have e3 : k + 1 + 2 = k + 3 := by omega
  have e4 : k + 1 + 1 = k + 2 := by omega
  rw [e1, e2] at h1; rw [e3, e4] at h2
  linear_combination h1 + (2 * a) * h2 + h3
private theorem stormU_nonneg_lt_succ (a : ℤ) (ha : 2 ≤ a) (k : ℕ) :
    0 ≤ stormU a k ∧ stormU a k < stormU a (k + 1) := by
  induction k with
  | zero => simp [stormU]
  | succ k ih =>
    have hrec := stormU_succ2 a k
    have e : k + 1 + 1 = k + 2 := by omega
    rw [e]
    refine ⟨by linarith [ih.1, ih.2], ?_⟩
    rw [hrec]
    nlinarith [ih.1, ih.2, ha]

private theorem stormU_nonneg (a : ℤ) (ha : 2 ≤ a) (k : ℕ) : 0 ≤ stormU a k :=
  (stormU_nonneg_lt_succ a ha k).1

private theorem stormU_lt_succ (a : ℤ) (ha : 2 ≤ a) (k : ℕ) :
    stormU a k < stormU a (k + 1) :=
  (stormU_nonneg_lt_succ a ha k).2

private theorem stormU_gt_self (a : ℤ) (ha : 2 ≤ a) (k : ℕ) (hk : 2 ≤ k) :
    (k : ℤ) < stormU a k := by
  induction k, hk using Nat.le_induction with
  | base => rw [stormU_two]; push_cast; linarith
  | succ k hk ih =>
    have hlt := stormU_lt_succ a ha k
    push_cast at ih ⊢; linarith
private theorem stormU_odd_congr_a (a : ℤ) (m : ℕ) :
    (a ^ 2 - 1) ∣ stormU a (2 * m + 1) - ((2 * m + 1 : ℕ) : ℤ) := by
  have P : ∀ m : ℕ, (a ^ 2 - 1) ∣ stormU a (2 * m + 1) - ((2 * m + 1 : ℕ) : ℤ) ∧
      (a ^ 2 - 1) ∣ stormU a (2 * (m + 1) + 1) - ((2 * (m + 1) + 1 : ℕ) : ℤ) := by
    intro m
    induction m with
    | zero =>
      constructor
      · simp [stormU]
      · have h3 := stormU_three a
        have e : (2 * (0 + 1) + 1 : ℕ) = 3 := by omega
        rw [e, h3]
        exact ⟨4, by push_cast; ring⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have hrec := stormU_twostep a (2 * m + 1)
      have e1 : 2 * m + 1 + 4 = 2 * (m + 1 + 1) + 1 := by omega
      have e2 : 2 * m + 1 + 2 = 2 * (m + 1) + 1 := by omega
      rw [e1, e2] at hrec
      obtain ⟨s, hs⟩ := ih.1
      obtain ⟨s', hs'⟩ := ih.2
      have i1 : ((2 * m + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 1 := by push_cast; ring
      have i2 : ((2 * (m + 1) + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 3 := by push_cast; ring
      have i3 : ((2 * (m + 1 + 1) + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 5 := by push_cast; ring
      rw [i1] at hs; rw [i2] at hs'; rw [i3]
      refine ⟨2 * s' - s + 4 * stormU a (2 * (m + 1) + 1), ?_⟩
      linear_combination hrec - hs + 2 * hs'
  exact (P m).1
private theorem stormU_odd_congr_b (a : ℤ) (m : ℕ) :
    ∃ r : ℤ, 3 * stormU a (2 * m + 1)
      = 3 * ((2 * m + 1 : ℕ) : ℤ)
        + 2 * (m : ℤ) * ((m : ℤ) + 1) * (((2 * m + 1 : ℕ) : ℤ)) * (a ^ 2 - 1)
        + r * (a ^ 2 - 1) ^ 2 := by
  have P : ∀ m : ℕ,
      (∃ r : ℤ, 3 * stormU a (2 * m + 1)
        = 3 * ((2 * m + 1 : ℕ) : ℤ)
          + 2 * (m : ℤ) * ((m : ℤ) + 1) * (((2 * m + 1 : ℕ) : ℤ)) * (a ^ 2 - 1)
          + r * (a ^ 2 - 1) ^ 2) ∧
      (∃ r : ℤ, 3 * stormU a (2 * (m + 1) + 1)
        = 3 * ((2 * (m + 1) + 1 : ℕ) : ℤ)
          + 2 * ((m : ℤ) + 1) * ((m : ℤ) + 2) * (((2 * (m + 1) + 1 : ℕ) : ℤ)) * (a ^ 2 - 1)
          + r * (a ^ 2 - 1) ^ 2) := by
    intro m
    induction m with
    | zero =>
      constructor
      · refine ⟨0, by simp [stormU]⟩
      · refine ⟨0, ?_⟩
        have h3 := stormU_three a
        have e : (2 * (0 + 1) + 1 : ℕ) = 3 := by omega
        rw [e, h3]
        push_cast; ring
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨r, hr⟩ := ih.1
      obtain ⟨r', hr'⟩ := ih.2
      have hrec := stormU_twostep a (2 * m + 1)
      have e1 : 2 * m + 1 + 4 = 2 * (m + 1 + 1) + 1 := by omega
      have e2 : 2 * m + 1 + 2 = 2 * (m + 1) + 1 := by omega
      rw [e1, e2] at hrec
      have c1 : ((2 * m + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 1 := by push_cast; ring
      have c2 : ((2 * (m + 1) + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 3 := by push_cast; ring
      have c3 : ((2 * (m + 1 + 1) + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 5 := by push_cast; ring
      have c5 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [c1] at hr
      rw [c2] at hr'
      rw [c3, c5]
      refine ⟨4 * (2 * ((m : ℤ) + 1) * ((m : ℤ) + 2) * (2 * (m : ℤ) + 3))
        + 2 * r' + 4 * (a ^ 2 - 1) * r' - r, ?_⟩
      linear_combination (2 + 4 * (a ^ 2 - 1)) * hr' - hr + 3 * hrec
  exact (P m).1
private theorem natPrime_not_dvd_int_one {q : ℕ} (hq : q.Prime) (h : (q : ℤ) ∣ 1) : False := by
  have h2 : q ∣ 1 := by exact_mod_cast h
  exact hq.not_dvd_one h2

private theorem natPrime_eq_of_dvd_int_three {q : ℕ} (hq : q.Prime) (h : (q : ℤ) ∣ 3) : q = 3 := by
  have h2 : q ∣ 3 := by exact_mod_cast h
  have h3 : Nat.Prime 3 := by norm_num
  exact (Nat.prime_dvd_prime_iff_eq hq h3).mp h2

private theorem stormU_two_newprime (a : ℤ) (ha : 2 ≤ a) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ stormU a 2 ∧ ¬ (q : ℤ) ∣ a ^ 2 - 1 := by
  have hne : a.natAbs ≠ 1 := by
    have : 2 ≤ a.natAbs := by
      have h := Int.le_natAbs (a := a); omega
    omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
  have hqa : (q : ℤ) ∣ a := by
    have h1 : (q : ℤ) ∣ ((a.natAbs : ℕ) : ℤ) := by exact_mod_cast hqdvd
    rw [Int.natCast_natAbs, abs_of_nonneg (by linarith)] at h1
    exact h1
  refine ⟨q, hq, by rw [stormU_two]; exact dvd_mul_of_dvd_right hqa 2, ?_⟩
  intro hcon
  have h1 : (q : ℤ) ∣ (1 : ℤ) := by
    have h2 : (q : ℤ) ∣ a * a := dvd_mul_of_dvd_left hqa a
    have h3 : a * a - (a ^ 2 - 1) = 1 := by ring
    have h4 : (q : ℤ) ∣ a * a - (a ^ 2 - 1) := dvd_sub h2 hcon
    rwa [h3] at h4
  exact natPrime_not_dvd_int_one hq h1

private theorem stormU_three_newprime (a : ℤ) (ha : 2 ≤ a) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ stormU a 3 ∧ ¬ (q : ℤ) ∣ a ^ 2 - 1 := by
  have h32 : ¬ (3 : ℤ) ∣ (2 : ℤ) := by decide
  -- choose f ∈ {2a-1, 2a+1} not divisible by 3
  have hchoice : (¬ (3 : ℤ) ∣ 2 * a - 1) ∨ (¬ (3 : ℤ) ∣ 2 * a + 1) := by
    by_cases h : (3 : ℤ) ∣ 2 * a - 1
    · right
      intro hc2
      have hsub : (3 : ℤ) ∣ (2 * a + 1) - (2 * a - 1) := dvd_sub hc2 h
      have heq : (2 * a + 1 : ℤ) - (2 * a - 1) = 2 := by ring
      rw [heq] at hsub
      exact h32 hsub
    · exact Or.inl h
  -- unify the two cases: f with 3 ∤ f, f ≥ 3, and (f = 2a-1 ∨ f = 2a+1)
  obtain ⟨f, hf3, hfge, hfeq⟩ : ∃ f : ℤ, ¬ (3 : ℤ) ∣ f ∧ 3 ≤ f ∧
      (f = 2 * a - 1 ∨ f = 2 * a + 1) := by
    rcases hchoice with h | h
    · exact ⟨2 * a - 1, h, by linarith, Or.inl rfl⟩
    · exact ⟨2 * a + 1, h, by linarith, Or.inr rfl⟩
  have hne : f.natAbs ≠ 1 := by
    have hle : 3 ≤ f.natAbs := by
      have h := Int.le_natAbs (a := f); omega
    omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
  have hqf : (q : ℤ) ∣ f := by
    have h1 : (q : ℤ) ∣ ((f.natAbs : ℕ) : ℤ) := by exact_mod_cast hqdvd
    rw [Int.natCast_natAbs, abs_of_nonneg (by linarith)] at h1
    exact h1
  have hqU : (q : ℤ) ∣ stormU a 3 := by
    rw [stormU_three]
    have hdiv : f ∣ 4 * a ^ 2 - 1 := by
      rcases hfeq with rfl | rfl
      · exact ⟨2 * a + 1, by ring⟩
      · exact ⟨2 * a - 1, by ring⟩
    exact dvd_trans hqf hdiv
  have hqne3 : q ≠ 3 := by
    intro hqq
    subst hqq
    exact hf3 hqf
  refine ⟨q, hq, hqU, ?_⟩
  intro hcon
  have hfac : a ^ 2 - 1 = (a - 1) * (a + 1) := by ring
  rw [hfac] at hcon
  have hprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  rcases (Prime.dvd_mul hprime).mp hcon with hqa1 | hqa2
  · -- q ∣ a-1
    rcases hfeq with rfl | rfl
    · -- f = 2a-1: (2a-1) - 2(a-1) = 1
      have h1 : (q : ℤ) ∣ (1 : ℤ) := by
        have h2 : (q : ℤ) ∣ (2 * a - 1) - 2 * (a - 1) :=
          dvd_sub hqf (dvd_mul_of_dvd_right hqa1 2)
        have h3 : (2 * a - 1 : ℤ) - 2 * (a - 1) = 1 := by ring
        rwa [h3] at h2
      exact natPrime_not_dvd_int_one hq h1
    · -- f = 2a+1: (2a+1) - 2(a-1) = 3
      have h1 : (q : ℤ) ∣ (3 : ℤ) := by
        have h2 : (q : ℤ) ∣ (2 * a + 1) - 2 * (a - 1) :=
          dvd_sub hqf (dvd_mul_of_dvd_right hqa1 2)
        have h3 : (2 * a + 1 : ℤ) - 2 * (a - 1) = 3 := by ring
        rwa [h3] at h2
      exact hqne3 (natPrime_eq_of_dvd_int_three hq h1)
  · -- q ∣ a+1
    rcases hfeq with rfl | rfl
    · -- f = 2a-1: 2(a+1) - (2a-1) = 3
      have h1 : (q : ℤ) ∣ (3 : ℤ) := by
        have h2 : (q : ℤ) ∣ 2 * (a + 1) - (2 * a - 1) :=
          dvd_sub (dvd_mul_of_dvd_right hqa2 2) hqf
        have h3 : (2 : ℤ) * (a + 1) - (2 * a - 1) = 3 := by ring
        rwa [h3] at h2
      exact hqne3 (natPrime_eq_of_dvd_int_three hq h1)
    · -- f = 2a+1: 2(a+1) - (2a+1) = 1
      have h1 : (q : ℤ) ∣ (1 : ℤ) := by
        have h2 : (q : ℤ) ∣ 2 * (a + 1) - (2 * a + 1) :=
          dvd_sub (dvd_mul_of_dvd_right hqa2 2) hqf
        have h3 : (2 : ℤ) * (a + 1) - (2 * a + 1) = 1 := by ring
        rwa [h3] at h2
      exact natPrime_not_dvd_int_one hq h1
private theorem pell_pow_eq (d : ℤ) (c : Pell.Solution₁ d) (k : ℕ) :
    (c ^ k).y = c.y * stormU c.x k ∧
    (c ^ k).x = stormU c.x (k + 1) - c.x * stormU c.x k := by
  induction k with
  | zero =>
    constructor
    · simp [pow_zero, Pell.Solution₁.y_one, stormU]
    · simp [pow_zero, Pell.Solution₁.x_one, stormU]
  | succ k ih =>
    obtain ⟨ihy, ihx⟩ := ih
    have hrec := stormU_succ2 c.x k
    have hprop := c.prop_y
    have hx : (c ^ k * c).x = (c ^ k).x * c.x + d * ((c ^ k).y * c.y) :=
      Pell.Solution₁.x_mul _ _
    have hy : (c ^ k * c).y = (c ^ k).x * c.y + (c ^ k).y * c.x :=
      Pell.Solution₁.y_mul _ _
    have e : k + 1 + 1 = k + 2 := by omega
    rw [pow_succ]
    constructor
    · rw [hy, ihx, ihy]; ring
    · rw [e, hx, ihx, ihy]
      linear_combination stormU c.x k * hprop - hrec
private theorem stormU_five_newprime (a : ℤ) (ha : 2 ≤ a) (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ stormU a p ∧ ¬ (q : ℤ) ∣ a ^ 2 - 1 := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨m, rfl⟩ := hp.odd_of_ne_two hp2
  have hm5 : 5 ≤ 2 * m + 1 := hp5
  have ht1 : (1 : ℤ) ≤ ((2 * m + 1 : ℕ) : ℤ) := by exact_mod_cast (by omega : 1 ≤ 2 * m + 1)
  have hu_nonneg : 0 ≤ stormU a (2 * m + 1) := stormU_nonneg a ha _
  have hu_gt : ((2 * m + 1 : ℕ) : ℤ) < stormU a (2 * m + 1) :=
    stormU_gt_self a ha _ (by omega)
  by_contra hnone
  have h : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ stormU a (2 * m + 1) → (q : ℤ) ∣ a ^ 2 - 1 := by
    intro q hqp hqu
    by_contra hne
    exact hnone ⟨q, hqp, hqu, hne⟩
  have claim1 : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ stormU a (2 * m + 1) → q = 2 * m + 1 := by
    intro q hqp hqu
    have hqe : (q : ℤ) ∣ a ^ 2 - 1 := h q hqp hqu
    obtain ⟨d1, hd1⟩ := stormU_odd_congr_a a m
    have hut : (q : ℤ) ∣ stormU a (2 * m + 1) - ((2 * m + 1 : ℕ) : ℤ) := by
      rw [hd1]; exact dvd_mul_of_dvd_left hqe d1
    have hqt : (q : ℤ) ∣ ((2 * m + 1 : ℕ) : ℤ) := by
      have hsub : (q : ℤ) ∣ stormU a (2 * m + 1) - (stormU a (2 * m + 1) - ((2 * m + 1 : ℕ) : ℤ)) :=
        dvd_sub hqu hut
      rwa [sub_sub_cancel] at hsub
    have hN : q ∣ 2 * m + 1 := by exact_mod_cast hqt
    exact (Nat.prime_dvd_prime_iff_eq hqp hp).mp hN
  have claim2 : ((2 * m + 1 : ℕ) : ℤ) ∣ a ^ 2 - 1 := by
    have h1u : (1 : ℤ) < stormU a (2 * m + 1) := lt_of_le_of_lt ht1 hu_gt
    have hune : (stormU a (2 * m + 1)).natAbs ≠ 1 := by
      have hle : 1 < (stormU a (2 * m + 1)).natAbs := by
        have hle2 := Int.le_natAbs (a := stormU a (2 * m + 1)); omega
      omega
    obtain ⟨q0, hq0, hq0dvd⟩ := Nat.exists_prime_and_dvd hune
    have hq0u : (q0 : ℤ) ∣ stormU a (2 * m + 1) := by
      have h1 : (q0 : ℤ) ∣ (((stormU a (2 * m + 1)).natAbs : ℕ) : ℤ) := by exact_mod_cast hq0dvd
      rw [Int.natCast_natAbs, abs_of_nonneg hu_nonneg] at h1
      exact h1
    have e1 : q0 = 2 * m + 1 := claim1 q0 hq0 hq0u
    have hq0e := h q0 hq0 hq0u
    rwa [e1] at hq0e
  have claim3 : ¬ (((2 * m + 1 : ℕ) : ℤ)) ^ 2 ∣ stormU a (2 * m + 1) := by
    intro hsq
    obtain ⟨r, hr⟩ := stormU_odd_congr_b a m
    obtain ⟨s, hs⟩ := claim2
    have ht0 : ((2 * m + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : 2 * m + 1 ≠ 0)
    have hfe : (((2 * m + 1 : ℕ) : ℤ)) ^ 2 ∣
        2 * (m : ℤ) * ((m : ℤ) + 1) * (((2 * m + 1 : ℕ) : ℤ)) * (a ^ 2 - 1) := by
      refine ⟨2 * (m : ℤ) * ((m : ℤ) + 1) * s, ?_⟩
      linear_combination 2 * (m : ℤ) * ((m : ℤ) + 1) * ((2 * m + 1 : ℕ) : ℤ) * hs
    have hre : (((2 * m + 1 : ℕ) : ℤ)) ^ 2 ∣ r * (a ^ 2 - 1) ^ 2 := by
      refine ⟨r * s ^ 2, ?_⟩
      linear_combination r * ((a ^ 2 - 1) + ((2 * m + 1 : ℕ) : ℤ) * s) * hs
    have h3u : (((2 * m + 1 : ℕ) : ℤ)) ^ 2 ∣ 3 * stormU a (2 * m + 1) - 3 *
        ((2 * m + 1 : ℕ) : ℤ) := by
      have heq : 3 * stormU a (2 * m + 1) - 3 * ((2 * m + 1 : ℕ) : ℤ)
          = (2 * (m : ℤ) * ((m : ℤ) + 1) * (((2 * m + 1 : ℕ) : ℤ)) * (a ^ 2 - 1)) +
              (r * (a ^ 2 - 1) ^ 2) := by
        linear_combination hr
      rw [heq]; exact dvd_add hfe hre
    have hmu : (((2 * m + 1 : ℕ) : ℤ)) ^ 2 ∣ 3 * stormU a (2 * m + 1) := by
      obtain ⟨v, hv⟩ := hsq; exact ⟨3 * v, by rw [hv]; ring⟩
    have h3t : (((2 * m + 1 : ℕ) : ℤ)) ^ 2 ∣ 3 * ((2 * m + 1 : ℕ) : ℤ) := by
      have hsub := dvd_sub hmu h3u
      rwa [show 3 * stormU a (2 * m + 1) - (3 * stormU a (2 * m + 1) - 3 * ((2 * m + 1 : ℕ) : ℤ))
        = 3 * ((2 * m + 1 : ℕ) : ℤ) from by ring] at hsub
    obtain ⟨c, hc⟩ := h3t
    have htc : ((2 * m + 1 : ℕ) : ℤ) * 3 = ((2 * m + 1 : ℕ) : ℤ) * (((2 * m + 1 : ℕ) : ℤ) * c) := by
      linear_combination hc
    have htdvd3 : ((2 * m + 1 : ℕ) : ℤ) ∣ 3 := ⟨c, mul_left_cancel₀ ht0 htc⟩
    have hN : 2 * m + 1 ∣ 3 := by exact_mod_cast htdvd3
    have hle := Nat.le_of_dvd (by norm_num) hN
    omega
  -- finish: u = t * w with w > 1
  obtain ⟨s2, hs2⟩ := claim2
  obtain ⟨d1, hd1⟩ := stormU_odd_congr_a a m
  have htu : ((2 * m + 1 : ℕ) : ℤ) ∣ stormU a (2 * m + 1) := by
    refine ⟨1 + s2 * d1, ?_⟩
    linear_combination hd1 + d1 * hs2
  obtain ⟨w, hw⟩ := htu
  have hw1 : (1 : ℤ) < w := by
    by_contra hc
    have hwle : w ≤ 1 := not_lt.mp hc
    have htle : ((2 * m + 1 : ℕ) : ℤ) * w ≤ ((2 * m + 1 : ℕ) : ℤ) * 1 :=
      mul_le_mul_of_nonneg_left hwle (by exact_mod_cast (by omega : 0 ≤ 2 * m + 1))
    rw [mul_one] at htle
    rw [hw] at hu_gt
    linarith
  have hntw : ¬ ((2 * m + 1 : ℕ) : ℤ) ∣ w := by
    intro htw
    obtain ⟨v, hv⟩ := htw
    have hsq : (((2 * m + 1 : ℕ) : ℤ)) ^ 2 ∣ stormU a (2 * m + 1) := by
      refine ⟨v, by rw [hw, hv]; ring⟩
    exact claim3 hsq
  have hwne : w.natAbs ≠ 1 := by
    have hle : 1 < w.natAbs := by
      have hle2 := Int.le_natAbs (a := w); omega
    omega
  obtain ⟨q1, hq1, hq1dvd⟩ := Nat.exists_prime_and_dvd hwne
  have hqw : (q1 : ℤ) ∣ w := by
    have h1 : (q1 : ℤ) ∣ ((w.natAbs : ℕ) : ℤ) := by exact_mod_cast hq1dvd
    rw [Int.natCast_natAbs, abs_of_nonneg (by linarith)] at h1
    exact h1
  have hq1u : (q1 : ℤ) ∣ stormU a (2 * m + 1) := by
    rw [hw]; exact dvd_mul_of_dvd_right hqw ((2 * m + 1 : ℕ) : ℤ)
  have e1 : q1 = 2 * m + 1 := claim1 q1 hq1 hq1u
  rw [e1] at hqw
  exact hntw hqw
private theorem stormU_prime_newprime (a : ℤ) (ha : 2 ≤ a) (p : ℕ) (hp : p.Prime) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ stormU a p ∧ ¬ (q : ℤ) ∣ a ^ 2 - 1 := by
  by_cases h2 : p = 2
  · subst h2; exact stormU_two_newprime a ha
  · by_cases h3 : p = 3
    · subst h3; exact stormU_three_newprime a ha
    · exact stormU_five_newprime a ha p hp (hp.five_le_of_ne_two_of_ne_three h2 h3)

private theorem pell_pow_y_newprime (d : ℤ) (hd : 0 < d) (c : Pell.Solution₁ d)
    (hcx : 0 < c.x) (hcy : 0 < c.y) (k : ℕ) (hk : 2 ≤ k) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ (c ^ k).y ∧ ¬ (q : ℤ) ∣ d := by
  have hk1 : k ≠ 1 := by omega
  have hpp : (k.minFac).Prime := Nat.minFac_prime hk1
  obtain ⟨j, hj⟩ := Nat.minFac_dvd k
  have hp2 : 2 ≤ k.minFac := hpp.two_le
  have hj1 : 1 ≤ j := by
    by_contra hc
    have hj0 : j = 0 := by omega
    rw [hj0, mul_zero] at hj
    omega
  have hetax : (0 : ℤ) < (c ^ j).x := Pell.Solution₁.x_pow_pos hcx j
  have hetay : (0 : ℤ) < (c ^ j).y := by
    have h := Pell.Solution₁.y_pow_succ_pos hcx hcy (j - 1)
    rwa [show (j - 1).succ = j from by omega] at h
  have heta2 : 2 ≤ (c ^ j).x := by
    have hsq : (0 : ℤ) < ((c ^ j).y) ^ 2 := by
      rw [pow_two]; exact mul_self_pos.mpr (ne_of_gt hetay)
    have hxx := (c ^ j).prop_x
    have h1d : (1 : ℤ) ≤ d := hd
    nlinarith [hxx, hsq, hetax, h1d]
  obtain ⟨q, hq, hqU, hqe⟩ := stormU_prime_newprime (c ^ j).x heta2 k.minFac hpp
  have hkk : k = j * k.minFac := hj.trans (mul_comm _ _)
  have hpow : c ^ k = (c ^ j) ^ k.minFac := by conv_lhs => rw [hkk]; rw [pow_mul]
  have hpeq := pell_pow_eq d (c ^ j) k.minFac
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hpow, hpeq.1]
    exact dvd_mul_of_dvd_right hqU (c ^ j).y
  · intro hqd
    have hdm : (q : ℤ) ∣ d * (c ^ j).y ^ 2 := dvd_mul_of_dvd_left hqd _
    rw [(c ^ j).prop_y] at hdm
    exact hqe hdm

private theorem pell_rad_unique (d : ℤ) (hd : 0 < d) (a b : Pell.Solution₁ d)
    (hax : 0 < a.x) (hay : 0 < a.y) (hbx : 0 < b.x) (hby : 0 < b.y)
    (ha : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ a.y → (q : ℤ) ∣ d)
    (hb : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ b.y → (q : ℤ) ∣ d) : a = b := by
  have one_lt : ∀ s : Pell.Solution₁ d, 0 < s.x → 0 < s.y → 1 < s.x := by
    intro s hsx hsy
    have hne : s.y ≠ 0 := ne_of_gt hsy
    have hpos : (0 : ℤ) < s.y ^ 2 := by
      rw [pow_two]; exact mul_self_pos.mpr hne
    have h1d : (1 : ℤ) ≤ d := hd
    nlinarith [s.prop_x, hpos, hsx, h1d]
  have hnsq : ¬ IsSquare d :=
    Pell.Solution₁.d_nonsquare_of_one_lt_x (one_lt a hax hay)
  obtain ⟨ε, hε⟩ := Pell.IsFundamental.exists_of_not_isSquare hd hnsq
  have key : ∀ s : Pell.Solution₁ d, 0 < s.x → 0 < s.y →
      (∀ q : ℕ, q.Prime → (q : ℤ) ∣ s.y → (q : ℤ) ∣ d) → s = ε := by
    intro s hsx hsy hs
    obtain ⟨m, hm⟩ := hε.eq_pow_of_nonneg hsx hsy.le
    by_cases hm0 : m = 0
    · subst hm0
      rw [hm, pow_zero, Pell.Solution₁.y_one] at hsy
      omega
    · by_cases hm1 : m = 1
      · subst hm1; rw [hm, pow_one]
      · have hm2 : 2 ≤ m := by omega
        obtain ⟨q, hq, hqy, hqd⟩ :=
          pell_pow_y_newprime d hd ε hε.x_pos hε.2.1 m hm2
        have hsy2 : (q : ℤ) ∣ s.y := by rw [hm]; exact hqy
        exact absurd (hs q hq hsy2) hqd
  rw [key a hax hay ha, key b hbx hby hb]
private theorem prime_dvd_primorial_of_le (y q : ℕ) (hq : q.Prime) (hle : q ≤ y) :
    q ∣ primorial y := by
  unfold primorial
  apply Finset.dvd_prod_of_mem (fun p => p)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hq⟩

private theorem prime_le_of_smooth_pair (y n q : ℕ) (hy : 2 ≤ y) (hn0 : 0 < n)
    (hn : ∀ p ∈ n.primeFactors, p ≤ y)
    (hn1 : ∀ p ∈ (n + 1).primeFactors, p ≤ y)
    (hq : q.Prime) (hqd : q ∣ 4 * n * (n + 1)) : q ≤ y ∧ q ∣ primorial y := by
  have hle : q ≤ y := by
    rcases hq.dvd_mul.mp hqd with h41 | hn1d
    · rcases hq.dvd_mul.mp h41 with h4 | hnd
      · have h2 : q ∣ 2 * 2 := by
          have h4e : (4 : ℕ) = 2 * 2 := by norm_num
          rwa [h4e] at h4
        have h1 : q ∣ 2 := (hq.dvd_mul.mp h2).elim id id
        have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h1
        omega
      · have hmem : q ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq, hnd, ne_of_gt hn0⟩
        exact hn q hmem
    · have hmem : q ∈ (n + 1).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq, hn1d, by omega⟩
      exact hn1 q hmem
  exact ⟨hle, prime_dvd_primorial_of_le y q hq hle⟩

private theorem exists_pell_rad_of_smooth (y n : ℕ) (hy : 2 ≤ y) (hn0 : 0 < n)
    (hn : ∀ p ∈ n.primeFactors, p ≤ y)
    (hn1 : ∀ p ∈ (n + 1).primeFactors, p ≤ y) :
    ∃ D ∈ (primorial y ^ 3).divisors, ∃ Y : ℕ, 0 < Y ∧
      ((2 * n + 1 : ℕ) : ℤ) ^ 2 - (D : ℤ) * (Y : ℤ) ^ 2 = 1 ∧
      ∀ q : ℕ, q.Prime → q ∣ Y → q ∣ D := by
  have hN : 0 < 4 * n * (n + 1) := by positivity
  obtain ⟨a, b, ha0, hb0, hsq, hsf⟩ := Nat.sq_mul_squarefree_of_pos hN
  set g := Nat.gcd b (primorial y) with hg_def
  set Y := b / g with hY_def
  set D := a * g ^ 2 with hD_def
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left (primorial y) hb0
  have hgb : g ∣ b := Nat.gcd_dvd_left b (primorial y)
  have hgQ : g ∣ primorial y := Nat.gcd_dvd_right b (primorial y)
  have hbg : b = Y * g := (Nat.div_mul_cancel hgb).symm
  have hY0 : 0 < Y := Nat.div_pos (Nat.le_of_dvd hb0 hgb) hg0
  have hle2 : ∀ r : ℕ, r.Prime → r ∣ 4 * n * (n + 1) → r ≤ y ∧ r ∣ primorial y :=
    fun r hr hrd => prime_le_of_smooth_pair y n r hy hn0 hn hn1 hr hrd
  have haQ : a ∣ primorial y := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsf]
    apply Finset.prod_dvd_prod_of_subset _ _ (fun p => p)
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range]
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
    have hpN : p ∣ 4 * n * (n + 1) := by
      have h1 : p ∣ b ^ 2 * a := dvd_mul_of_dvd_right hpa (b ^ 2)
      rwa [hsq] at h1
    have hple : p ≤ y := (hle2 p (Nat.prime_of_mem_primeFactors hp) hpN).1
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact ⟨by omega, hpp⟩
  have hDQ : D ∣ primorial y ^ 3 := by
    have h3 : primorial y ^ 3 = primorial y * primorial y ^ 2 := by ring
    rw [hD_def, h3]
    exact mul_dvd_mul haQ (pow_dvd_pow_of_dvd hgQ 2)
  have hDmem : D ∈ (primorial y ^ 3).divisors := by
    rw [Nat.mem_divisors]
    refine ⟨hDQ, ?_⟩
    exact pow_ne_zero 3 (ne_of_gt (primorial_pos y))
  refine ⟨D, hDmem, Y, hY0, ?_, ?_⟩
  · have hDY : D * Y ^ 2 = 4 * n * (n + 1) := by
      have e1 : D * Y ^ 2 = a * (Y * g) ^ 2 := by rw [hD_def]; ring
      rw [e1, ← hbg, mul_comm a (b ^ 2), hsq]
    have h1 : ((2 * n + 1 : ℕ) : ℤ) ^ 2 = 4 * (n : ℤ) * ((n : ℤ) + 1) + 1 := by
      push_cast; ring
    have h2 : ((D * Y ^ 2 : ℕ) : ℤ) = 4 * (n : ℤ) * ((n : ℤ) + 1) := by
      rw [hDY]; push_cast; ring
    have h2' : (D : ℤ) * (Y : ℤ) ^ 2 = 4 * (n : ℤ) * ((n : ℤ) + 1) := by
      have := h2; push_cast at this ⊢; linear_combination this
    linear_combination h1 - h2'
  · intro q hqp hqY
    have hYb : Y ∣ b := ⟨g, hbg⟩
    have hqb : q ∣ b := dvd_trans hqY hYb
    have hbN : b ∣ 4 * n * (n + 1) := ⟨b * a, by rw [← hsq]; ring⟩
    have hqN : q ∣ 4 * n * (n + 1) := dvd_trans hqb hbN
    have hqQ : q ∣ primorial y := (hle2 q hqp hqN).2
    have hqg : q ∣ g := Nat.dvd_gcd hqb hqQ
    have hg2 : g ∣ g ^ 2 := ⟨g, by ring⟩
    rw [hD_def]
    exact dvd_mul_of_dvd_right (dvd_trans hqg hg2) a
/-- Stormer's theorem (stormer-s1): for each fixed smoothness bound `y ≥ 2`, there are only
finitely many pairs of consecutive positive integers both of which are `y`-smooth
(all prime factors `≤ y`), witnessed by an explicit finite bound `S`.
Source: https://en.wikipedia.org/wiki/St%C3%B8rmer%27s_theorem.

Proves `Wanted` entry `stormer_theorem`.
-/
theorem stormer_theorem (y : ℕ) (hy : 2 ≤ y) :
    ∃ S : Finset (ℕ × ℕ), ∀ n : ℕ, 0 < n →
      (∀ p ∈ n.primeFactors, p ≤ y) →
      (∀ p ∈ (n + 1).primeFactors, p ≤ y) →
      (n, n + 1) ∈ S := by
  have hsub : {n : ℕ | 0 < n ∧ (∀ p ∈ n.primeFactors, p ≤ y) ∧
        (∀ p ∈ (n + 1).primeFactors, p ≤ y)} ⊆
      ⋃ D ∈ (↑((primorial y ^ 3).divisors) : Set ℕ),
        {n : ℕ | ∃ Y : ℕ, 0 < Y ∧ ((2 * n + 1 : ℕ) : ℤ) ^ 2 - (D : ℤ) * (Y : ℤ) ^ 2 = 1 ∧
          ∀ q : ℕ, q.Prime → q ∣ Y → q ∣ D} := by
    intro n hn
    obtain ⟨hn0, hn, hn1⟩ := hn
    obtain ⟨D, hD, Y, hY0, hpe, hrad⟩ := exists_pell_rad_of_smooth y n hy hn0 hn hn1
    exact Set.mem_biUnion hD ⟨Y, hY0, hpe, hrad⟩
  have hfib : ∀ D ∈ (↑((primorial y ^ 3).divisors) : Set ℕ),
      ({n : ℕ | ∃ Y : ℕ, 0 < Y ∧ ((2 * n + 1 : ℕ) : ℤ) ^ 2 - (D : ℤ) * (Y : ℤ) ^ 2 = 1 ∧
        ∀ q : ℕ, q.Prime → q ∣ Y → q ∣ D} : Set ℕ).Subsingleton := by
    intro D hD n1 hn1 n2 hn2
    obtain ⟨Y1, hY1, hpe1, hrad1⟩ := hn1
    obtain ⟨Y2, hY2, hpe2, hrad2⟩ := hn2
    have hD0 : (0 : ℤ) < D := by
      exact_mod_cast Nat.pos_of_mem_divisors (Finset.mem_coe.mp hD)
    have e : Pell.Solution₁.mk ((2 * n1 + 1 : ℕ) : ℤ) (Y1 : ℤ) hpe1
        = Pell.Solution₁.mk ((2 * n2 + 1 : ℕ) : ℤ) (Y2 : ℤ) hpe2 := by
      apply pell_rad_unique _ hD0
      · rw [Pell.Solution₁.x_mk]; exact_mod_cast (by omega : 0 < 2 * n1 + 1)
      · rw [Pell.Solution₁.y_mk]; exact_mod_cast hY1
      · rw [Pell.Solution₁.x_mk]; exact_mod_cast (by omega : 0 < 2 * n2 + 1)
      · rw [Pell.Solution₁.y_mk]; exact_mod_cast hY2
      · intro q hqp hqy
        rw [Pell.Solution₁.y_mk] at hqy
        have hqY : q ∣ Y1 := by exact_mod_cast hqy
        have hqD : q ∣ D := hrad1 q hqp hqY
        exact_mod_cast hqD
      · intro q hqp hqy
        rw [Pell.Solution₁.y_mk] at hqy
        have hqY : q ∣ Y2 := by exact_mod_cast hqy
        have hqD : q ∣ D := hrad2 q hqp hqY
        exact_mod_cast hqD
    have hx : ((2 * n1 + 1 : ℕ) : ℤ) = ((2 * n2 + 1 : ℕ) : ℤ) := by
      have hxx := congrArg Pell.Solution₁.x e
      rwa [Pell.Solution₁.x_mk, Pell.Solution₁.x_mk] at hxx
    have heq : 2 * n1 + 1 = 2 * n2 + 1 := by exact_mod_cast hx
    omega
  have hfin : {n : ℕ | 0 < n ∧ (∀ p ∈ n.primeFactors, p ≤ y) ∧
      (∀ p ∈ (n + 1).primeFactors, p ≤ y)}.Finite :=
    Set.Finite.subset
      (Set.Finite.biUnion (Finset.finite_toSet _) (fun D hD => (hfib D hD).finite)) hsub
  refine ⟨hfin.toFinset.image (fun n => (n, n + 1)), ?_⟩
  intro n hn0 hn hn1
  rw [Finset.mem_image]
  exact ⟨n, (Set.Finite.mem_toFinset hfin).mpr ⟨hn0, hn, hn1⟩, rfl⟩

end
end MetaMathlibExt
