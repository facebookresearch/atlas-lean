/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt.HappySix
/-- Sum of squares of decimal digits. Literal Wanted expression. -/
private def digitSqSum (n : ℕ) : ℕ :=
  (((Nat.digits 10 n).map (fun d => d ^ 2)).sum)

private theorem digitSqSum_ten_mul_add (q d : ℕ) (hd : d < 10) :
    digitSqSum (10 * q + d) = digitSqSum q + d ^ 2 := by
  unfold digitSqSum
  by_cases h : d = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp [Nat.digits_zero]
  · have hne : d ≠ 0 ∨ q ≠ 0 := by
      rcases eq_or_ne d 0 with rfl | hd0
      · rcases eq_or_ne q 0 with rfl | hq0
        · exfalso; exact h ⟨rfl, rfl⟩
        · exact Or.inr hq0
      · exact Or.inl hd0
    have hdig : Nat.digits 10 (d + 10 * q) = d :: Nat.digits 10 q :=
      Nat.digits_add 10 (by norm_num) d q hd hne
    have heq : 10 * q + d = d + 10 * q := by omega
    rw [heq, hdig, List.map_cons, List.sum_cons, Nat.add_comm]

private theorem digitSqSum_zero : digitSqSum 0 = 0 := by
  unfold digitSqSum
  simp [Nat.digits_zero]

private theorem digitSqSum_single (d : ℕ) (hd : d < 10) (hd0 : d ≠ 0) :
    digitSqSum d = d ^ 2 := by
  unfold digitSqSum
  rw [Nat.digits_of_lt 10 d hd0 hd, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero]

private theorem digitSqSum_one : digitSqSum 1 = 1 := by
  have h := digitSqSum_single 1 (by norm_num) (by norm_num)
  simpa using h

private theorem digitSqSum_carry_low (q r j : ℕ) (h : r + j < 10) :
    digitSqSum (10 * q + r + j) = digitSqSum q + (r + j) ^ 2 := by
  have heq : 10 * q + r + j = 10 * q + (r + j) := by omega
  rw [heq]
  exact digitSqSum_ten_mul_add q (r + j) (by omega)

private theorem digitSqSum_carry_high (q r j : ℕ) (h1 : 10 ≤ r + j) (h2 : r + j < 20) :
    digitSqSum (10 * q + r + j) = digitSqSum (q + 1) + (r + j - 10) ^ 2 := by
  have heq : 10 * q + r + j = 10 * (q + 1) + (r + j - 10) := by omega
  rw [heq]
  exact digitSqSum_ten_mul_add (q + 1) (r + j - 10) (by omega)

private theorem digitSqSum_add_pow_mul (k : ℕ) : ∀ (x y : ℕ), x < 10 ^ k →
    digitSqSum (x + 10 ^ k * y) = digitSqSum x + digitSqSum y := by
  induction k with
  | zero =>
    intro x y hx
    simp only [pow_zero, Order.lt_one_iff]at hx
    subst hx
    simp [digitSqSum_zero]
  | succ k ih =>
    intro x y hx
    have hmod : x % 10 < 10 := Nat.mod_lt x (by norm_num)
    have hx10 : x < 10 * 10 ^ k := by
      have hps : 10 ^ (k + 1) = 10 * 10 ^ k := by rw [Nat.pow_succ']
      omega
    have hdiv : x / 10 < 10 ^ k := Nat.div_lt_of_lt_mul hx10
    have hdecomp : x = 10 * (x / 10) + x % 10 := by
      have := Nat.div_add_mod x 10
      omega
    have hps : 10 ^ (k + 1) = 10 ^ k * 10 := by rw [Nat.pow_succ]
    have hbig : x + 10 ^ (k + 1) * y = 10 * (x / 10 + 10 ^ k * y) + x % 10 := by
      conv_lhs => rw [hdecomp, hps]
      ring
    have lhs : digitSqSum (x + 10 ^ (k + 1) * y)
        = digitSqSum (x / 10 + 10 ^ k * y) + (x % 10) ^ 2 := by
      rw [hbig]
      exact digitSqSum_ten_mul_add _ _ hmod
    have rhs : digitSqSum x = digitSqSum (x / 10) + (x % 10) ^ 2 := by
      conv_lhs => rw [hdecomp]
      exact digitSqSum_ten_mul_add _ _ hmod
    rw [lhs, rhs, ih _ _ hdiv]
    ring

private theorem digitSqSum_pow_mul (k y : ℕ) :
    digitSqSum (10 ^ k * y) = digitSqSum y := by
  have h0 : (0 : ℕ) < 10 ^ k := Nat.pow_pos (by norm_num)
  have h := digitSqSum_add_pow_mul k 0 y h0
  simpa [digitSqSum_zero] using h

private theorem digitSqSum_nines (k : ℕ) : digitSqSum (10 ^ k - 1) = 81 * k := by
  induction k with
  | zero => simp [digitSqSum_zero]
  | succ k ih =>
    have hge : (1 : ℕ) ≤ 10 ^ k := Nat.one_le_pow k 10 (by norm_num)
    have heq : 10 ^ (k + 1) - 1 = 10 * (10 ^ k - 1) + 9 := by
      have hps : 10 ^ (k + 1) = 10 * 10 ^ k := by rw [Nat.pow_succ']
      omega
    rw [heq, digitSqSum_ten_mul_add _ _ (by norm_num), ih]
    ring

private theorem digitSqSum_le_of_lt_pow (n : ℕ) : ∀ (x : ℕ), x < 10 ^ n →
    digitSqSum x ≤ 81 * n := by
  induction n with
  | zero =>
    intro x hx
    simp only [pow_zero, Order.lt_one_iff]at hx
    subst hx
    unfold digitSqSum
    simp [Nat.digits_zero]
  | succ n ih =>
    intro x hx
    have hmod : x % 10 < 10 := Nat.mod_lt x (by norm_num)
    have hx10 : x < 10 * 10 ^ n := by
      have hps : 10 ^ (n + 1) = 10 * 10 ^ n := by rw [Nat.pow_succ']
      omega
    have hdiv : x / 10 < 10 ^ n := Nat.div_lt_of_lt_mul hx10
    have hdecomp : x = 10 * (x / 10) + x % 10 := by
      have := Nat.div_add_mod x 10
      omega
    have hSq : digitSqSum x = digitSqSum (x / 10) + (x % 10) ^ 2 := by
      conv_lhs => rw [hdecomp]
      exact digitSqSum_ten_mul_add _ _ hmod
    have h1 := ih _ hdiv
    have h2 : (x % 10) ^ 2 ≤ 81 := by
      have hle : x % 10 ≤ 9 := by omega
      have := Nat.pow_le_pow_left hle 2
      simpa using this
    omega

private theorem digit_deficit_cases (d : ℕ) (hd : d < 10) (hle : 81 - d ^ 2 ≤ 64) :
    (81 - d ^ 2 = 0 ∨ 81 - d ^ 2 = 17 ∨ 81 - d ^ 2 = 32 ∨ 81 - d ^ 2 = 45 ∨
     81 - d ^ 2 = 56) := by
  interval_cases d <;> omega

private theorem W_closed (w e : ℕ)
    (hw : w = 0 ∨ w = 17 ∨ w = 32 ∨ w = 34 ∨ w = 45 ∨ w = 49 ∨ w = 51 ∨ w = 56 ∨
      w = 62 ∨ w = 64)
    (he : e = 0 ∨ e = 17 ∨ e = 32 ∨ e = 45 ∨ e = 56)
    (hle : w + e ≤ 64) :
    (w + e = 0 ∨ w + e = 17 ∨ w + e = 32 ∨ w + e = 34 ∨ w + e = 45 ∨
     w + e = 49 ∨ w + e = 51 ∨ w + e = 56 ∨ w + e = 62 ∨ w + e = 64) := by
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases he with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem digitSqSum_deficit_mem (n : ℕ) : ∀ (x : ℕ), x < 10 ^ n →
    81 * n - digitSqSum x ≤ 64 →
    (81 * n - digitSqSum x = 0 ∨ 81 * n - digitSqSum x = 17 ∨
     81 * n - digitSqSum x = 32 ∨ 81 * n - digitSqSum x = 34 ∨
     81 * n - digitSqSum x = 45 ∨ 81 * n - digitSqSum x = 49 ∨
     81 * n - digitSqSum x = 51 ∨ 81 * n - digitSqSum x = 56 ∨
     81 * n - digitSqSum x = 62 ∨ 81 * n - digitSqSum x = 64) := by
  induction n with
  | zero =>
    intro x hx hle
    simp only [pow_zero, Order.lt_one_iff]at hx
    subst hx
    unfold digitSqSum
    simp [Nat.digits_zero]
  | succ n ih =>
    intro x hx hle
    have hmod : x % 10 < 10 := Nat.mod_lt x (by norm_num)
    have hx10 : x < 10 * 10 ^ n := by
      have hps : 10 ^ (n + 1) = 10 * 10 ^ n := by rw [Nat.pow_succ']
      omega
    have hdiv : x / 10 < 10 ^ n := Nat.div_lt_of_lt_mul hx10
    have hdecomp : x = 10 * (x / 10) + x % 10 := by
      have := Nat.div_add_mod x 10
      omega
    have hSq : digitSqSum x = digitSqSum (x / 10) + (x % 10) ^ 2 := by
      conv_lhs => rw [hdecomp]
      exact digitSqSum_ten_mul_add _ _ hmod
    have hle1 : digitSqSum (x / 10) ≤ 81 * n :=
      digitSqSum_le_of_lt_pow n _ hdiv
    have hdig : (x % 10) ^ 2 ≤ 81 := by
      have hle' : x % 10 ≤ 9 := by omega
      have := Nat.pow_le_pow_left hle' 2
      simpa using this
    have hD1 : 81 * n - digitSqSum (x / 10) ≤ 64 := by omega
    have hD2 : 81 - (x % 10) ^ 2 ≤ 64 := by omega
    have hmem1 := ih _ hdiv hD1
    have hmem2 := digit_deficit_cases _ hmod hD2
    have hsplit : 81 * (n + 1) - digitSqSum x
        = (81 * n - digitSqSum (x / 10)) + (81 - (x % 10) ^ 2) := by
      omega
    rw [hsplit]
    exact W_closed _ _ hmem1 hmem2 (by omega)

private theorem sq_eq_81 (d : ℕ) (_hd : d < 10) (h : d ^ 2 = 81) : d = 9 := by
  interval_cases d <;> omega

private theorem eq_pow_sub_one_of_digitSqSum_eq (n : ℕ) : ∀ (x : ℕ), x < 10 ^ n →
    digitSqSum x = 81 * n → x = 10 ^ n - 1 := by
  induction n with
  | zero =>
    intro x hx _
    simp only [pow_zero, Order.lt_one_iff]at hx
    subst hx
    simp
  | succ n ih =>
    intro x hx hS
    have hmod : x % 10 < 10 := Nat.mod_lt x (by norm_num)
    have hx10 : x < 10 * 10 ^ n := by
      have hps : 10 ^ (n + 1) = 10 * 10 ^ n := by rw [Nat.pow_succ']
      omega
    have hdiv : x / 10 < 10 ^ n := Nat.div_lt_of_lt_mul hx10
    have hdecomp : x = 10 * (x / 10) + x % 10 := by
      have := Nat.div_add_mod x 10
      omega
    have hSq : digitSqSum x = digitSqSum (x / 10) + (x % 10) ^ 2 := by
      conv_lhs => rw [hdecomp]
      exact digitSqSum_ten_mul_add _ _ hmod
    have hle1 : digitSqSum (x / 10) ≤ 81 * n :=
      digitSqSum_le_of_lt_pow n _ hdiv
    have hdig : (x % 10) ^ 2 ≤ 81 := by
      have hle' : x % 10 ≤ 9 := by omega
      have := Nat.pow_le_pow_left hle' 2
      simpa using this
    have hq : digitSqSum (x / 10) = 81 * n := by omega
    have hd9 : (x % 10) ^ 2 = 81 := by omega
    have hd : x % 10 = 9 := sq_eq_81 _ hmod hd9
    have ihx := ih _ hdiv hq
    have hge : (1 : ℕ) ≤ 10 ^ n := Nat.one_le_pow n 10 (by norm_num)
    have hps : 10 ^ (n + 1) = 10 * 10 ^ n := by rw [Nat.pow_succ']
    omega

private def IsHap (n : ℕ) : Prop :=
  ∃ k : ℕ, ∃ f : ℕ → ℕ,
    f 0 = n ∧ f k = 1 ∧ ∀ i : ℕ, i < k → f (i + 1) = digitSqSum (f i)

private theorem isHap_iff_exists_iterate (n : ℕ) :
    IsHap n ↔ ∃ k : ℕ, (digitSqSum^[k]) n = 1 := by
  constructor
  · rintro ⟨k, f, h0, hk, hstep⟩
    refine ⟨k, ?_⟩
    have hfi : ∀ i : ℕ, i ≤ k → f i = (digitSqSum^[i]) n := by
      intro i hi
      induction i with
      | zero =>
        simpa [Function.iterate_zero_apply] using h0
      | succ i ih =>
        have hlt : i < k := by omega
        have hi' : i ≤ k := by omega
        have e1 := ih hi'
        have e2 := hstep i hlt
        rw [e2, e1, Function.iterate_succ_apply']
    have := hfi k (by omega)
    omega
  · rintro ⟨k, hk⟩
    refine ⟨k, fun i => (digitSqSum^[i]) n, ?_, hk, ?_⟩
    · simp [Function.iterate_zero_apply]
    · intro i _
      exact Function.iterate_succ_apply' digitSqSum i n

private theorem isHap_digitSqSum (n : ℕ) (h : IsHap n) : IsHap (digitSqSum n) := by
  rw [isHap_iff_exists_iterate] at h ⊢
  obtain ⟨k, hk⟩ := h
  rcases k with _ | k'
  · simp only [Function.iterate_zero_apply] at hk
    subst hk
    refine ⟨0, ?_⟩
    simp [Function.iterate_zero_apply, digitSqSum_one]
  · refine ⟨k', ?_⟩
    have hsk : (digitSqSum^[k' + 1]) n = (digitSqSum^[k']) (digitSqSum n) :=
      Function.iterate_succ_apply digitSqSum k' n
    omega

/-- Unhappiness certificate: true if some iterate within fuel hits 0 or 4. -/
private def unhCert : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, n => if n = 0 then true else if n = 4 then true else unhCert k (digitSqSum n)

private def Cmem (c : ℕ) : Prop :=
  c = 0 ∨ c = 4 ∨ c = 16 ∨ c = 37 ∨ c = 58 ∨ c = 89 ∨ c = 145 ∨ c = 42 ∨ c = 20

private theorem digitSqSum_maps_C (c : ℕ) (hc : Cmem c) : Cmem (digitSqSum c) := by
  unfold Cmem at hc ⊢
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem iterate_mem_C (j c : ℕ) (hc : Cmem c) : Cmem ((digitSqSum^[j]) c) := by
  induction j with
  | zero =>
    simpa [Function.iterate_zero_apply] using hc
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact digitSqSum_maps_C _ ih

private theorem one_not_mem_C : ¬ Cmem 1 := by
  unfold Cmem
  rintro (h | h | h | h | h | h | h | h | h) <;> omega

private theorem unhCert_hit (k n : ℕ) (h : unhCert k n = true) :
    ∃ i : ℕ, ((digitSqSum^[i]) n = 0 ∨ (digitSqSum^[i]) n = 4) := by
  induction k generalizing n with
  | zero =>
    simp [unhCert] at h
  | succ k ih =>
    unfold unhCert at h
    by_cases hn0 : n = 0
    · subst hn0
      exact ⟨0, Or.inl (by simp [Function.iterate_zero_apply])⟩
    · simp only [hn0, ↓reduceIte, Bool.ite_true_left, Bool.or_eq_true, decide_eq_true_eq] at h
      by_cases hn4 : n = 4
      · subst hn4
        exact ⟨0, Or.inr (by simp [Function.iterate_zero_apply])⟩
      · simp only [hn4, false_or] at h
        obtain ⟨i, hi⟩ := ih _ h
        refine ⟨i + 1, ?_⟩
        have e : (digitSqSum^[i + 1]) n = (digitSqSum^[i]) (digitSqSum n) :=
          Function.iterate_succ_apply digitSqSum i n
        rw [e]
        exact hi

private theorem not_isHap_of_unhCert (k n : ℕ) (h : unhCert k n = true) : ¬ IsHap n := by
  rw [isHap_iff_exists_iterate]
  rintro ⟨t, ht⟩
  obtain ⟨i, hi⟩ := unhCert_hit k n h
  by_cases hle : t ≤ i
  · have hadd : (digitSqSum^[i]) n
        = (digitSqSum^[i - t]) ((digitSqSum^[t]) n) := by
      have e := Function.iterate_add_apply digitSqSum (i - t) t n
      have hii : i - t + t = i := by omega
      rw [hii] at e
      exact e
    rw [ht, Function.iterate_fixed digitSqSum_one (i - t)] at hadd
    omega
  · have hlt : i < t := by omega
    have hadd : (digitSqSum^[t]) n
        = (digitSqSum^[t - i]) ((digitSqSum^[i]) n) := by
      have e := Function.iterate_add_apply digitSqSum (t - i) i n
      have hii : t - i + i = t := by omega
      rw [hii] at e
      exact e
    have hmem : Cmem ((digitSqSum^[t - i]) ((digitSqSum^[i]) n)) := by
      rcases hi with h0 | h4
      · rw [h0]
        exact iterate_mem_C _ _ (Or.inl rfl)
      · rw [h4]
        exact iterate_mem_C _ _ (Or.inr (Or.inl rfl))
    rw [ht] at hadd
    rw [← hadd] at hmem
    exact one_not_mem_C hmem

/-- Happiness certificate: true if some iterate within fuel hits 1. -/
private def hapCert : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, n => if n = 1 then true else hapCert k (digitSqSum n)

private theorem isHap_of_hapCert (k n : ℕ) (h : hapCert k n = true) : IsHap n := by
  induction k generalizing n with
  | zero =>
    simp [hapCert] at h
  | succ k ih =>
    unfold hapCert at h
    by_cases hn : n = 1
    · subst hn
      rw [isHap_iff_exists_iterate]
      exact ⟨0, by simp [Function.iterate_zero_apply]⟩
    · simp only [hn, ↓reduceIte] at h
      have hmem := ih _ h
      rw [isHap_iff_exists_iterate] at hmem ⊢
      obtain ⟨i, hi⟩ := hmem
      refine ⟨i + 1, ?_⟩
      have e : (digitSqSum^[i + 1]) n = (digitSqSum^[i]) (digitSqSum n) :=
        Function.iterate_succ_apply digitSqSum i n
      rw [e]
      exact hi

private theorem exists_trailing_nines_decomp (q : ℕ) :
    ∃ t w e : ℕ, e ≤ 8 ∧ q = 10 ^ t * (10 * w + e) + (10 ^ t - 1) ∧
      digitSqSum q = digitSqSum w + e ^ 2 + 81 * t ∧
      digitSqSum (q + 1) = digitSqSum w + (e + 1) ^ 2 ∧
      q + 1 = 10 ^ t * (10 * w + (e + 1)) ∧
      ∀ r : ℕ, 10 * q + r ≥ 10 ^ (t + 2) * w := by
  refine Nat.strong_induction_on q ?_
  intro q ih
  have hmod : q % 10 < 10 := Nat.mod_lt q (by norm_num)
  have hdm := Nat.div_add_mod q 10
  by_cases h9 : q % 10 = 9
  · -- trailing nine: peel off and use IH on q / 10
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at h9
    have hlt : q / 10 < q := Nat.div_lt_self (by omega) (by norm_num)
    obtain ⟨t', w, e, he8, hmain, hS, hS1, hsucc, hbound⟩ := ih _ hlt
    have hq : q = 10 * (q / 10) + 9 := by omega
    have hps : 10 ^ (t' + 1) = 10 * 10 ^ t' := by rw [Nat.pow_succ']
    have hge : 1 ≤ 10 ^ t' := Nat.one_le_pow t' 10 (by norm_num)
    have e1 : 10 ^ (t' + 1) - 1 = 10 * (10 ^ t' - 1) + 9 := by omega
    have e2 : 10 ^ (t' + 1) * (10 * w + e) = 10 * (10 ^ t' * (10 * w + e)) := by
      rw [hps]; ring
    have hmain' : q = 10 ^ (t' + 1) * (10 * w + e) + (10 ^ (t' + 1) - 1) := by
      rw [e1, e2]
      omega
    have hSq9 : digitSqSum q = digitSqSum (q / 10) + 9 ^ 2 := by
      conv_lhs => rw [hq]
      exact digitSqSum_ten_mul_add _ _ (by norm_num)
    have h81 : (9 : ℕ) ^ 2 = 81 := by norm_num
    rw [h81] at hSq9
    have hS' : digitSqSum q = digitSqSum w + e ^ 2 + 81 * (t' + 1) := by
      omega
    have hq1 : q + 1 = 10 * (q / 10 + 1) := by omega
    have e3 : 10 * (10 ^ t' * (10 * w + (e + 1)))
        = 10 ^ (t' + 1) * (10 * w + (e + 1)) := by
      rw [hps]; ring
    have hsucc' : q + 1 = 10 ^ (t' + 1) * (10 * w + (e + 1)) := by
      rw [hq1, hsucc, e3]
    have hSq1 : digitSqSum (q + 1) = digitSqSum (10 * w + (e + 1)) := by
      rw [hq1, hsucc, e3, digitSqSum_pow_mul]
    have he1 : e + 1 < 10 := by omega
    have hS1' : digitSqSum (q + 1) = digitSqSum w + (e + 1) ^ 2 := by
      rw [hSq1]
      exact digitSqSum_ten_mul_add _ _ he1
    have h10 : 10 ^ (t' + 1 + 2) = 10 ^ (t' + 1) * 100 := by
      rw [Nat.pow_add]
    have hqge : 10 ^ (t' + 1) * (10 * w + e) ≤ q := by omega
    have hbound' : ∀ r : ℕ, 10 * q + r ≥ 10 ^ (t' + 1 + 2) * w := by
      intro r
      have hle100 : 100 * w ≤ 10 * (10 * w + e) := by omega
      have e4 : 10 ^ (t' + 1) * 100 * w
          ≤ 10 * (10 ^ (t' + 1) * (10 * w + e)) := by
        calc 10 ^ (t' + 1) * 100 * w = 10 ^ (t' + 1) * (100 * w) := by ring
          _ ≤ 10 ^ (t' + 1) * (10 * (10 * w + e)) :=
              Nat.mul_le_mul_left _ hle100
          _ = 10 * (10 ^ (t' + 1) * (10 * w + e)) := by ring
      rw [h10]
      omega
    exact ⟨t' + 1, w, e, he8, hmain', hS', hS1', hsucc', hbound'⟩
  · -- no trailing nine
    have he8 : q % 10 ≤ 8 := by omega
    have hqA : q = 10 * (q / 10) + q % 10 := by omega
    have hmain : q = 10 ^ 0 * (10 * (q / 10) + q % 10) + (10 ^ 0 - 1) := by
      have h0 : (10 : ℕ) ^ 0 = 1 := by norm_num
      rw [h0]
      omega
    have hSqA : digitSqSum q = digitSqSum (q / 10) + (q % 10) ^ 2 := by
      conv_lhs => rw [hqA]
      exact digitSqSum_ten_mul_add _ _ hmod
    have hS : digitSqSum q = digitSqSum (q / 10) + (q % 10) ^ 2 + 81 * 0 := by
      omega
    have hq1 : q + 1 = 10 * (q / 10) + (q % 10 + 1) := by omega
    have he1 : q % 10 + 1 < 10 := by omega
    have hS1 : digitSqSum (q + 1) = digitSqSum (q / 10) + (q % 10 + 1) ^ 2 := by
      conv_lhs => rw [hq1]
      exact digitSqSum_ten_mul_add _ _ he1
    have hsucc : q + 1 = 10 ^ 0 * (10 * (q / 10) + (q % 10 + 1)) := by
      have h0 : (10 : ℕ) ^ 0 = 1 := by norm_num
      rw [h0]
      omega
    have hbound : ∀ r : ℕ, 10 * q + r ≥ 10 ^ (0 + 2) * (q / 10) := by
      intro r
      have h02 : (10 : ℕ) ^ (0 + 2) = 100 := by norm_num
      rw [h02]
      omega
    exact ⟨0, q / 10, q % 10, he8, hmain, hS, hS1, hsucc, hbound⟩

private theorem bound_of_digitSqSum_300 (w : ℕ) (h : digitSqSum w = 300) : 10 ^ 4 ≤ w := by
  by_contra hcon
  have hlt : w < 10 ^ 4 := not_le.mp hcon
  have hdef : 81 * 4 - digitSqSum w = 24 := by omega
  have hmem := digitSqSum_deficit_mem 4 w hlt (by omega)
  rw [hdef] at hmem
  omega

private theorem bound_of_digitSqSum_588 (w : ℕ) (h : digitSqSum w = 588) : 10 ^ 8 ≤ w := by
  by_contra hcon
  have hlt : w < 10 ^ 8 := not_le.mp hcon
  have hdef : 81 * 8 - digitSqSum w = 60 := by omega
  have hmem := digitSqSum_deficit_mem 8 w hlt (by omega)
  rw [hdef] at hmem
  omega

private theorem bound_of_digitSqSum_1398 (w : ℕ) (h : digitSqSum w = 1398) : 10 ^ 18 ≤ w := by
  by_contra hcon
  have hlt : w < 10 ^ 18 := not_le.mp hcon
  have hdef : 81 * 18 - digitSqSum w = 60 := by omega
  have hmem := digitSqSum_deficit_mem 18 w hlt (by omega)
  rw [hdef] at hmem
  omega

private theorem bound_of_digitSqSum_1722 (w : ℕ) (h : digitSqSum w = 1722) : 10 ^ 22 ≤ w := by
  by_contra hcon
  have hlt : w < 10 ^ 22 := not_le.mp hcon
  have hdef : 81 * 22 - digitSqSum w = 60 := by omega
  have hmem := digitSqSum_deficit_mem 22 w hlt (by omega)
  rw [hdef] at hmem
  omega
private theorem le_of_digitSqSum_eq_1085 (w : ℕ) (h : digitSqSum w = 1085) :
    78999999999999 ≤ w := by
  by_contra hcon
  have hlt : w < 78999999999999 := not_le.mp hcon
  have h13 : (10 : ℕ) ^ 13 = 10000000000000 := by norm_num
  have h12 : (10 : ℕ) ^ 12 = 1000000000000 := by norm_num
  by_cases hw13 : w < 10 ^ 13
  · have hle := digitSqSum_le_of_lt_pow 13 w hw13
    omega
  · have hge13 : 10 ^ 13 ≤ w := not_lt.mp hw13
    have hpos13 : (0 : ℕ) < 10000000000000 := by norm_num
    set d := w / 10000000000000 with hd_def
    set x := w % 10000000000000 with hx_def
    have hdm13 : x + 10000000000000 * d = w := by
      rw [hx_def, hd_def]
      exact Nat.mod_add_div w 10000000000000
    have hd1 : 1 ≤ d := by
      rw [hd_def]
      have h13w : 10000000000000 ≤ w := by omega
      have := Nat.div_pos h13w hpos13
      omega
    have hd7 : d ≤ 7 := by
      rw [hd_def]
      have hub : w < 8 * 10000000000000 := by omega
      have := Nat.div_lt_iff_lt_mul hpos13 |>.mpr hub
      omega
    have hx13 : x < 10 ^ 13 := by
      rw [h13, hx_def]
      exact Nat.mod_lt w hpos13
    have hwd : w = x + 10 ^ 13 * d := by
      rw [h13]
      omega
    have hN2 := digitSqSum_add_pow_mul 13 x d hx13
    rw [← hwd, h] at hN2
    -- hN2 : digitSqSum x + digitSqSum d = 1085
    have hSd : digitSqSum d = d ^ 2 := by
      rcases eq_or_ne d 0 with h0 | hne
      · rw [h0]
        simp [digitSqSum_zero]
      · exact digitSqSum_single d (by omega) hne
    have hd2 : d ^ 2 ≤ 49 := by
      have hh := Nat.pow_le_pow_left hd7 2
      norm_num at hh
      exact hh
    have hSx : digitSqSum x = 1085 - d ^ 2 := by omega
    have hSx_le : digitSqSum x ≤ 81 * 13 :=
      digitSqSum_le_of_lt_pow 13 x hx13
    have hd6 : 6 ≤ d := by
      by_contra hc6
      have hle5 : d ≤ 5 := by omega
      have hh := Nat.pow_le_pow_left hle5 2
      norm_num at hh
      omega
    have hd67 : d = 6 ∨ d = 7 := by omega
    rcases hd67 with h6 | h7
    · -- d = 6: deficit of x is 4, not in W
      rw [h6] at hSx
      have h36 : (6 : ℕ) ^ 2 = 36 := by norm_num
      rw [h36] at hSx
      have hdef : 81 * 13 - digitSqSum x = 4 := by omega
      have hmem := digitSqSum_deficit_mem 13 x hx13 (by omega)
      rw [hdef] at hmem
      omega
    · -- d = 7: second leading digit analysis
      rw [h7] at hSx
      have h49 : (7 : ℕ) ^ 2 = 49 := by norm_num
      rw [h49] at hSx
      -- hSx : digitSqSum x = 1036
      have hx1036 : digitSqSum x = 1036 := by omega
      have hx8999 : x < 8999999999999 := by omega
      have hpos12 : (0 : ℕ) < 1000000000000 := by norm_num
      set d' := x / 1000000000000 with hd'_def
      set y := x % 1000000000000 with hy_def
      have hdm12 : y + 1000000000000 * d' = x := by
        rw [hy_def, hd'_def]
        exact Nat.mod_add_div x 1000000000000
      have hd'8 : d' ≤ 8 := by
        rw [hd'_def]
        have hub : x < 9 * 1000000000000 := by omega
        have := Nat.div_lt_iff_lt_mul hpos12 |>.mpr hub
        omega
      have hy12 : y < 10 ^ 12 := by
        rw [h12, hy_def]
        exact Nat.mod_lt x hpos12
      have hxeq : x = y + 10 ^ 12 * d' := by
        rw [h12]
        omega
      have hN2' := digitSqSum_add_pow_mul 12 y d' hy12
      rw [← hxeq, hx1036] at hN2'
      have hSd' : digitSqSum d' = d' ^ 2 := by
        rcases eq_or_ne d' 0 with h0' | hne
        · rw [h0']
          simp [digitSqSum_zero]
        · exact digitSqSum_single d' (by omega) hne
      have hd'2 : d' ^ 2 ≤ 1036 := by
        have hh := Nat.pow_le_pow_left hd'8 2
        norm_num at hh
        omega
      have hSy : digitSqSum y = 1036 - d' ^ 2 := by omega
      have hSy_le : digitSqSum y ≤ 81 * 12 :=
        digitSqSum_le_of_lt_pow 12 y hy12
      have hd'e : d' = 8 := by
        by_cases h8 : d' = 8
        · exact h8
        · have hle7 : d' ≤ 7 := by omega
          have hh := Nat.pow_le_pow_left hle7 2
          norm_num at hh
          omega
      rw [hd'e] at hSy
      have h64 : (8 : ℕ) ^ 2 = 64 := by norm_num
      rw [h64] at hSy
      have hSy972 : digitSqSum y = 81 * 12 := by omega
      have hy_eq := eq_pow_sub_one_of_digitSqSum_eq 12 y hy12 hSy972
      rw [h12] at hy_eq
      omega
private theorem table_T1_0 : ∀ a < 2026, ∃ j < 6,
    unhCert 20 (a + (0 + j) ^ 2) = true := by
  decide +kernel

private theorem table_T1_1 : ∀ a < 2026, ∃ j < 6,
    unhCert 20 (a + (1 + j) ^ 2) = true := by
  decide +kernel

private theorem table_T1_2 : ∀ a < 2026, ∃ j < 6,
    unhCert 20 (a + (2 + j) ^ 2) = true := by
  decide +kernel

private theorem table_T1_3 : ∀ a < 2026, ∃ j < 6,
    unhCert 20 (a + (3 + j) ^ 2) = true := by
  decide +kernel

private theorem table_T1_4 : ∀ a < 2026, ∃ j < 6,
    unhCert 20 (a + (4 + j) ^ 2) = true := by
  decide +kernel

private theorem table_T2 : ∀ a < 2026, ∃ d ∈ ([5, 6, 7, 8, 9] : List ℕ),
    unhCert 20 (a + d ^ 2) = true := by
  decide +kernel

private theorem table_T3 : ∀ b < 2026, ∃ d ∈ ([0, 1, 2, 3] : List ℕ),
    unhCert 20 (b + d ^ 2) = true := by
  decide +kernel

private theorem table_T4 : ∀ a < 2026, a ≠ 1839 →
    ∃ d ∈ ([6, 7, 8, 9] : List ℕ), unhCert 20 (a + d ^ 2) = true := by
  decide +kernel

private theorem table_T5 : ∀ a < 2026, a ≠ 568 → a ≠ 574 → a ≠ 1839 →
    ∃ d ∈ ([7, 8, 9] : List ℕ), unhCert 20 (a + d ^ 2) = true := by
  decide +kernel

private theorem no_happy_run_of_residue (q r : ℕ) (hr : r < 10) (hr6 : r ≠ 6)
    (hr7 : r ≠ 7) (hSq : digitSqSum q ≤ 2025)
    (hSq1 : digitSqSum (q + 1) ≤ 2025)
    (hall : ∀ j : ℕ, j < 6 → IsHap (digitSqSum (10 * q + r + j))) : False := by
  interval_cases r
  · obtain ⟨j, hj6, hjcert⟩ := table_T1_0 (digitSqSum q) (by omega)
    have heq := digitSqSum_carry_low q 0 j (by omega)
    have h1 := hall j hj6
    rw [heq] at h1
    exact not_isHap_of_unhCert 20 _ hjcert h1
  · obtain ⟨j, hj6, hjcert⟩ := table_T1_1 (digitSqSum q) (by omega)
    have heq := digitSqSum_carry_low q 1 j (by omega)
    have h1 := hall j hj6
    rw [heq] at h1
    exact not_isHap_of_unhCert 20 _ hjcert h1
  · obtain ⟨j, hj6, hjcert⟩ := table_T1_2 (digitSqSum q) (by omega)
    have heq := digitSqSum_carry_low q 2 j (by omega)
    have h1 := hall j hj6
    rw [heq] at h1
    exact not_isHap_of_unhCert 20 _ hjcert h1
  · obtain ⟨j, hj6, hjcert⟩ := table_T1_3 (digitSqSum q) (by omega)
    have heq := digitSqSum_carry_low q 3 j (by omega)
    have h1 := hall j hj6
    rw [heq] at h1
    exact not_isHap_of_unhCert 20 _ hjcert h1
  · obtain ⟨j, hj6, hjcert⟩ := table_T1_4 (digitSqSum q) (by omega)
    have heq := digitSqSum_carry_low q 4 j (by omega)
    have h1 := hall j hj6
    rw [heq] at h1
    exact not_isHap_of_unhCert 20 _ hjcert h1
  · -- r = 5
    obtain ⟨d, hdm, hdcert⟩ := table_T2 (digitSqSum q) (by omega)
    have hdd : d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by simpa using hdm
    rcases hdd with rfl | rfl | rfl | rfl | rfl
    · have heq := digitSqSum_carry_low q 5 0 (by norm_num)
      have h1 := hall 0 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
    · have heq := digitSqSum_carry_low q 5 1 (by norm_num)
      have h1 := hall 1 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
    · have heq := digitSqSum_carry_low q 5 2 (by norm_num)
      have h1 := hall 2 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
    · have heq := digitSqSum_carry_low q 5 3 (by norm_num)
      have h1 := hall 3 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
    · have heq := digitSqSum_carry_low q 5 4 (by norm_num)
      have h1 := hall 4 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
  · exact hr6 rfl
  · exact hr7 rfl
  · -- r = 8
    obtain ⟨d, hdm, hdcert⟩ := table_T3 (digitSqSum (q + 1)) (by omega)
    have hdd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by simpa using hdm
    rcases hdd with rfl | rfl | rfl | rfl
    · have heq := digitSqSum_carry_high q 8 2 (by norm_num) (by norm_num)
      have h1 := hall 2 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
    · have heq := digitSqSum_carry_high q 8 3 (by norm_num) (by norm_num)
      have h1 := hall 3 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
    · have heq := digitSqSum_carry_high q 8 4 (by norm_num) (by norm_num)
      have h1 := hall 4 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
    · have heq := digitSqSum_carry_high q 8 5 (by norm_num) (by norm_num)
      have h1 := hall 5 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
  · -- r = 9
    obtain ⟨d, hdm, hdcert⟩ := table_T3 (digitSqSum (q + 1)) (by omega)
    have hdd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by simpa using hdm
    rcases hdd with rfl | rfl | rfl | rfl
    · have heq := digitSqSum_carry_high q 9 1 (by norm_num) (by norm_num)
      have h1 := hall 1 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
    · have heq := digitSqSum_carry_high q 9 2 (by norm_num) (by norm_num)
      have h1 := hall 2 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
    · have heq := digitSqSum_carry_high q 9 3 (by norm_num) (by norm_num)
      have h1 := hall 3 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
    · have heq := digitSqSum_carry_high q 9 4 (by norm_num) (by norm_num)
      have h1 := hall 4 (by norm_num)
      rw [heq] at h1
      exact not_isHap_of_unhCert 20 _ hdcert h1
private theorem table_T6_0 : ∀ t < 23, 0 ^ 2 + 81 * t ≤ 1839 → t ≠ 19 →
    ∃ d ∈ ([0, 1] : List ℕ),
      unhCert 20 (1839 - 0 ^ 2 - 81 * t + (0 + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T6_1 : ∀ t < 23, 1 ^ 2 + 81 * t ≤ 1839 →
    ∃ d ∈ ([0, 1] : List ℕ),
      unhCert 20 (1839 - 1 ^ 2 - 81 * t + (1 + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T6_2 : ∀ t < 23, 2 ^ 2 + 81 * t ≤ 1839 →
    ∃ d ∈ ([0, 1] : List ℕ),
      unhCert 20 (1839 - 2 ^ 2 - 81 * t + (2 + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T6_3 : ∀ t < 23, 3 ^ 2 + 81 * t ≤ 1839 →
    ∃ d ∈ ([0, 1] : List ℕ),
      unhCert 20 (1839 - 3 ^ 2 - 81 * t + (3 + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T6_4 : ∀ t < 23, 4 ^ 2 + 81 * t ≤ 1839 →
    ∃ d ∈ ([0, 1] : List ℕ),
      unhCert 20 (1839 - 4 ^ 2 - 81 * t + (4 + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T6_5 : ∀ t < 23, 5 ^ 2 + 81 * t ≤ 1839 → t ≠ 9 →
    ∃ d ∈ ([0, 1] : List ℕ),
      unhCert 20 (1839 - 5 ^ 2 - 81 * t + (5 + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T6_6 : ∀ t < 23, 6 ^ 2 + 81 * t ≤ 1839 →
    ¬ (t = 1 ∨ t = 5 ∨ t = 15) →
    ∃ d ∈ ([0, 1] : List ℕ),
      unhCert 20 (1839 - 6 ^ 2 - 81 * t + (6 + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T6_7 : ∀ t < 23, 7 ^ 2 + 81 * t ≤ 1839 →
    ∃ d ∈ ([0, 1] : List ℕ),
      unhCert 20 (1839 - 7 ^ 2 - 81 * t + (7 + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T6_8 : ∀ t < 23, 8 ^ 2 + 81 * t ≤ 1839 →
    ∃ d ∈ ([0, 1] : List ℕ),
      unhCert 20 (1839 - 8 ^ 2 - 81 * t + (8 + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T7_568 : ∀ e < 9, ∀ t < 23, e ^ 2 + 81 * t ≤ 568 →
    ∃ d ∈ ([0, 1, 2] : List ℕ),
      unhCert 20 (568 - e ^ 2 - 81 * t + (e + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T7_574 : ∀ e < 9, ∀ t < 23, e ^ 2 + 81 * t ≤ 574 →
    ∃ d ∈ ([0, 1, 2] : List ℕ),
      unhCert 20 (574 - e ^ 2 - 81 * t + (e + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel

private theorem table_T7_1839 : ∀ e < 9, ∀ t < 23, e ^ 2 + 81 * t ≤ 1839 →
    ¬ (e = 5 ∧ t = 9) →
    ∃ d ∈ ([0, 1, 2] : List ℕ),
      unhCert 20 (1839 - e ^ 2 - 81 * t + (e + 1) ^ 2 + d ^ 2) = true := by
  decide +kernel
private theorem le_of_happy_run_six (q : ℕ) (hSq : digitSqSum q ≤ 2025)
    (hall : ∀ j : ℕ, j < 6 → IsHap (digitSqSum (10 * q + 6 + j))) :
    7899999999999959999999996 ≤ 10 * q + 6 := by
  have hSq1839 : digitSqSum q = 1839 := by
    by_contra hne
    obtain ⟨d, hdm, hdcert⟩ := table_T4 (digitSqSum q) (by omega) hne
    have hdd : d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by simpa using hdm
    have e0 := digitSqSum_carry_low q 6 0 (by norm_num)
    have e1 := digitSqSum_carry_low q 6 1 (by norm_num)
    have e2 := digitSqSum_carry_low q 6 2 (by norm_num)
    have e3 := digitSqSum_carry_low q 6 3 (by norm_num)
    have g0 := hall 0 (by norm_num)
    have g1 := hall 1 (by norm_num)
    have g2 := hall 2 (by norm_num)
    have g3 := hall 3 (by norm_num)
    rw [e0] at g0
    rw [e1] at g1
    rw [e2] at g2
    rw [e3] at g3
    rcases hdd with rfl | rfl | rfl | rfl
    · exact (not_isHap_of_unhCert 20 _ hdcert g0).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g1).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g2).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g3).elim
  have e4 := digitSqSum_carry_high q 6 4 (by norm_num) (by norm_num)
  have e5 := digitSqSum_carry_high q 6 5 (by norm_num) (by norm_num)
  obtain ⟨t, w, e, he8, hmain, hS, hS1, hsucc, hbound⟩ :=
    exists_trailing_nines_decomp q
  have hSw : digitSqSum w = 1839 - e ^ 2 - 81 * t := by omega
  have hguard : e ^ 2 + 81 * t ≤ 1839 := by omega
  have ht23 : t < 23 := by omega
  interval_cases e
  · -- e = 0
    have hB : digitSqSum (q + 1) = 1839 - 0 ^ 2 - 81 * t + (0 + 1) ^ 2 := by
      omega
    by_cases ht : t = 19
    · rw [ht] at hSw hbound
      have hSw300 : digitSqSum w = 300 := by omega
      have hw4 := bound_of_digitSqSum_300 w hSw300
      have hb := hbound 6
      have e1 : 10 ^ (19 + 2) * 10 ^ 4 = 10 ^ 25 := by norm_num
      have e2 : 10 ^ (19 + 2) * w ≥ 10 ^ (19 + 2) * 10 ^ 4 :=
        Nat.mul_le_mul_left _ hw4
      have hN0 : 7899999999999959999999996 ≤ 10 ^ 25 := by norm_num
      omega
    · obtain ⟨d, hdm, hdcert⟩ := table_T6_0 t ht23 hguard ht
      have hdd : d = 0 ∨ d = 1 := by simpa using hdm
      have g4 := hall 4 (by norm_num)
      have g5 := hall 5 (by norm_num)
      rw [e4, hB] at g4
      rw [e5, hB] at g5
      rcases hdd with rfl | rfl
      · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
      · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
  · -- e = 1
    have hB : digitSqSum (q + 1) = 1839 - 1 ^ 2 - 81 * t + (1 + 1) ^ 2 := by
      omega
    obtain ⟨d, hdm, hdcert⟩ := table_T6_1 t ht23 hguard
    have hdd : d = 0 ∨ d = 1 := by simpa using hdm
    have g4 := hall 4 (by norm_num)
    have g5 := hall 5 (by norm_num)
    rw [e4, hB] at g4
    rw [e5, hB] at g5
    rcases hdd with rfl | rfl
    · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
  · -- e = 2
    have hB : digitSqSum (q + 1) = 1839 - 2 ^ 2 - 81 * t + (2 + 1) ^ 2 := by
      omega
    obtain ⟨d, hdm, hdcert⟩ := table_T6_2 t ht23 hguard
    have hdd : d = 0 ∨ d = 1 := by simpa using hdm
    have g4 := hall 4 (by norm_num)
    have g5 := hall 5 (by norm_num)
    rw [e4, hB] at g4
    rw [e5, hB] at g5
    rcases hdd with rfl | rfl
    · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
  · -- e = 3
    have hB : digitSqSum (q + 1) = 1839 - 3 ^ 2 - 81 * t + (3 + 1) ^ 2 := by
      omega
    obtain ⟨d, hdm, hdcert⟩ := table_T6_3 t ht23 hguard
    have hdd : d = 0 ∨ d = 1 := by simpa using hdm
    have g4 := hall 4 (by norm_num)
    have g5 := hall 5 (by norm_num)
    rw [e4, hB] at g4
    rw [e5, hB] at g5
    rcases hdd with rfl | rfl
    · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
  · -- e = 4
    have hB : digitSqSum (q + 1) = 1839 - 4 ^ 2 - 81 * t + (4 + 1) ^ 2 := by
      omega
    obtain ⟨d, hdm, hdcert⟩ := table_T6_4 t ht23 hguard
    have hdd : d = 0 ∨ d = 1 := by simpa using hdm
    have g4 := hall 4 (by norm_num)
    have g5 := hall 5 (by norm_num)
    rw [e4, hB] at g4
    rw [e5, hB] at g5
    rcases hdd with rfl | rfl
    · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
  · -- e = 5
    have hB : digitSqSum (q + 1) = 1839 - 5 ^ 2 - 81 * t + (5 + 1) ^ 2 := by
      omega
    by_cases ht : t = 9
    · rw [ht] at hSw hmain
      have hSw1085 : digitSqSum w = 1085 := by omega
      have hw := le_of_digitSqSum_eq_1085 w hSw1085
      have h9 : (10 : ℕ) ^ 9 = 1000000000 := by norm_num
      rw [h9] at hmain
      omega
    · obtain ⟨d, hdm, hdcert⟩ := table_T6_5 t ht23 hguard ht
      have hdd : d = 0 ∨ d = 1 := by simpa using hdm
      have g4 := hall 4 (by norm_num)
      have g5 := hall 5 (by norm_num)
      rw [e4, hB] at g4
      rw [e5, hB] at g5
      rcases hdd with rfl | rfl
      · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
      · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
  · -- e = 6
    have hB : digitSqSum (q + 1) = 1839 - 6 ^ 2 - 81 * t + (6 + 1) ^ 2 := by
      omega
    by_cases ht : t = 1 ∨ t = 5 ∨ t = 15
    · rcases ht with rfl | rfl | rfl
      · -- t = 1, s = 1722
        have hSw1722 : digitSqSum w = 1722 := by omega
        have hw22 := bound_of_digitSqSum_1722 w hSw1722
        have hb := hbound 6
        have e1 : 10 ^ (1 + 2) * 10 ^ 22 = 10 ^ 25 := by norm_num
        have e2 : 10 ^ (1 + 2) * w ≥ 10 ^ (1 + 2) * 10 ^ 22 :=
          Nat.mul_le_mul_left _ hw22
        have hN0 : 7899999999999959999999996 ≤ 10 ^ 25 := by norm_num
        omega
      · -- t = 5, s = 1398
        have hSw1398 : digitSqSum w = 1398 := by omega
        have hw18 := bound_of_digitSqSum_1398 w hSw1398
        have hb := hbound 6
        have e1 : 10 ^ (5 + 2) * 10 ^ 18 = 10 ^ 25 := by norm_num
        have e2 : 10 ^ (5 + 2) * w ≥ 10 ^ (5 + 2) * 10 ^ 18 :=
          Nat.mul_le_mul_left _ hw18
        have hN0 : 7899999999999959999999996 ≤ 10 ^ 25 := by norm_num
        omega
      · -- t = 15, s = 588
        have hSw588 : digitSqSum w = 588 := by omega
        have hw8 := bound_of_digitSqSum_588 w hSw588
        have hb := hbound 6
        have e1 : 10 ^ (15 + 2) * 10 ^ 8 = 10 ^ 25 := by norm_num
        have e2 : 10 ^ (15 + 2) * w ≥ 10 ^ (15 + 2) * 10 ^ 8 :=
          Nat.mul_le_mul_left _ hw8
        have hN0 : 7899999999999959999999996 ≤ 10 ^ 25 := by norm_num
        omega
    · obtain ⟨d, hdm, hdcert⟩ := table_T6_6 t ht23 hguard ht
      have hdd : d = 0 ∨ d = 1 := by simpa using hdm
      have g4 := hall 4 (by norm_num)
      have g5 := hall 5 (by norm_num)
      rw [e4, hB] at g4
      rw [e5, hB] at g5
      rcases hdd with rfl | rfl
      · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
      · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
  · -- e = 7
    have hB : digitSqSum (q + 1) = 1839 - 7 ^ 2 - 81 * t + (7 + 1) ^ 2 := by
      omega
    obtain ⟨d, hdm, hdcert⟩ := table_T6_7 t ht23 hguard
    have hdd : d = 0 ∨ d = 1 := by simpa using hdm
    have g4 := hall 4 (by norm_num)
    have g5 := hall 5 (by norm_num)
    rw [e4, hB] at g4
    rw [e5, hB] at g5
    rcases hdd with rfl | rfl
    · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
  · -- e = 8
    have hB : digitSqSum (q + 1) = 1839 - 8 ^ 2 - 81 * t + (8 + 1) ^ 2 := by
      omega
    obtain ⟨d, hdm, hdcert⟩ := table_T6_8 t ht23 hguard
    have hdd : d = 0 ∨ d = 1 := by simpa using hdm
    have g4 := hall 4 (by norm_num)
    have g5 := hall 5 (by norm_num)
    rw [e4, hB] at g4
    rw [e5, hB] at g5
    rcases hdd with rfl | rfl
    · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
private theorem le_of_happy_run_seven (q : ℕ) (hSq : digitSqSum q ≤ 2025)
    (hall : ∀ j : ℕ, j < 6 → IsHap (digitSqSum (10 * q + 7 + j))) :
    7899999999999959999999996 ≤ 10 * q + 7 := by
  have hSqA : digitSqSum q = 568 ∨ digitSqSum q = 574 ∨ digitSqSum q = 1839 := by
    by_contra hcon
    have h1 : digitSqSum q ≠ 568 := by omega
    have h2 : digitSqSum q ≠ 574 := by omega
    have h3 : digitSqSum q ≠ 1839 := by omega
    obtain ⟨d, hdm, hdcert⟩ := table_T5 (digitSqSum q) (by omega) h1 h2 h3
    have hdd : d = 7 ∨ d = 8 ∨ d = 9 := by simpa using hdm
    have e0 := digitSqSum_carry_low q 7 0 (by norm_num)
    have e1 := digitSqSum_carry_low q 7 1 (by norm_num)
    have e2 := digitSqSum_carry_low q 7 2 (by norm_num)
    have g0 := hall 0 (by norm_num)
    have g1 := hall 1 (by norm_num)
    have g2 := hall 2 (by norm_num)
    rw [e0] at g0
    rw [e1] at g1
    rw [e2] at g2
    rcases hdd with rfl | rfl | rfl
    · exact (not_isHap_of_unhCert 20 _ hdcert g0).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g1).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g2).elim
  have e3 := digitSqSum_carry_high q 7 3 (by norm_num) (by norm_num)
  have e4 := digitSqSum_carry_high q 7 4 (by norm_num) (by norm_num)
  have e5 := digitSqSum_carry_high q 7 5 (by norm_num) (by norm_num)
  obtain ⟨t, w, e, he8, hmain, hS, hS1, hsucc, hbound⟩ :=
    exists_trailing_nines_decomp q
  have he9 : e < 9 := by omega
  have g3 := hall 3 (by norm_num)
  have g4 := hall 4 (by norm_num)
  have g5 := hall 5 (by norm_num)
  rcases hSqA with h568 | h574 | h1839
  · -- a = 568
    have hguard : e ^ 2 + 81 * t ≤ 568 := by omega
    have ht23 : t < 23 := by omega
    have hB : digitSqSum (q + 1) = 568 - e ^ 2 - 81 * t + (e + 1) ^ 2 := by
      omega
    obtain ⟨d, hdm, hdcert⟩ := table_T7_568 e he9 t ht23 hguard
    have hdd : d = 0 ∨ d = 1 ∨ d = 2 := by simpa using hdm
    rw [e3, hB] at g3
    rw [e4, hB] at g4
    rw [e5, hB] at g5
    rcases hdd with rfl | rfl | rfl
    · exact (not_isHap_of_unhCert 20 _ hdcert g3).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
  · -- a = 574
    have hguard : e ^ 2 + 81 * t ≤ 574 := by omega
    have ht23 : t < 23 := by omega
    have hB : digitSqSum (q + 1) = 574 - e ^ 2 - 81 * t + (e + 1) ^ 2 := by
      omega
    obtain ⟨d, hdm, hdcert⟩ := table_T7_574 e he9 t ht23 hguard
    have hdd : d = 0 ∨ d = 1 ∨ d = 2 := by simpa using hdm
    rw [e3, hB] at g3
    rw [e4, hB] at g4
    rw [e5, hB] at g5
    rcases hdd with rfl | rfl | rfl
    · exact (not_isHap_of_unhCert 20 _ hdcert g3).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
    · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim
  · -- a = 1839
    have hguard : e ^ 2 + 81 * t ≤ 1839 := by omega
    have ht23 : t < 23 := by omega
    have hB : digitSqSum (q + 1) = 1839 - e ^ 2 - 81 * t + (e + 1) ^ 2 := by
      omega
    have hSw : digitSqSum w = 1839 - e ^ 2 - 81 * t := by omega
    by_cases h59 : e = 5 ∧ t = 9
    · obtain ⟨rfl, rfl⟩ := h59
      have hSw1085 : digitSqSum w = 1085 := by omega
      have hw := le_of_digitSqSum_eq_1085 w hSw1085
      have h9 : (10 : ℕ) ^ 9 = 1000000000 := by norm_num
      rw [h9] at hmain
      omega
    · obtain ⟨d, hdm, hdcert⟩ := table_T7_1839 e he9 t ht23 hguard h59
      have hdd : d = 0 ∨ d = 1 ∨ d = 2 := by simpa using hdm
      rw [e3, hB] at g3
      rw [e4, hB] at g4
      rw [e5, hB] at g5
      rcases hdd with rfl | rfl | rfl
      · exact (not_isHap_of_unhCert 20 _ hdcert g3).elim
      · exact (not_isHap_of_unhCert 20 _ hdcert g4).elim
      · exact (not_isHap_of_unhCert 20 _ hdcert g5).elim

private theorem le_of_happy_run_residue_six_seven (q r : ℕ) (hr67 : r = 6 ∨ r = 7)
    (hSq : digitSqSum q ≤ 2025)
    (hall : ∀ j : ℕ, j < 6 → IsHap (digitSqSum (10 * q + r + j))) :
    7899999999999959999999996 ≤ 10 * q + r := by
  rcases hr67 with rfl | rfl
  · exact le_of_happy_run_six q hSq hall
  · exact le_of_happy_run_seven q hSq hall
end MetaMathlibExt.HappySix

section
namespace MetaMathlibExt

/-! # Happy six minimal start
-/

/-- **Smallest run of six consecutive happy numbers.** A natural number is happy when repeatedly
replacing it by the sum of the squares of its decimal digits reaches $1$ after finitely many
steps. Let $N_0 = 7899999999999959999999996$. The six consecutive integers
$N_0, N_0 + 1, \dots, N_0 + 5$ are all happy, and every natural number $m$ such that
$m, m + 1, \dots, m + 5$ are all happy satisfies $m \ge N_0$.

Proves `Wanted` entry `happy_six_min`.

Source: Robert Styer, "Smallest Examples of Strings of Consecutive Happy
Numbers," Journal of Integer Sequences 13 (2010), Article 10.6.3,
Proposition, lines 135–136,
https://cs.uwaterloo.ca/journals/JIS/VOL13/Styer/styer5.tex
-/
theorem happy_six_min :
  (∀ j : ℕ, j < 6 →
    ∃ k : ℕ, ∃ f : ℕ → ℕ,
      f 0 = (7899999999999959999999996 + j) ∧
      f k = 1 ∧
      ∀ i : ℕ, i < k →
        f (i + 1) = (((Nat.digits 10 (f i)).map (fun d => d ^ 2)).sum)) ∧
  ∀ m : ℕ,
    (∀ j : ℕ, j < 6 →
      ∃ k : ℕ, ∃ f : ℕ → ℕ,
        f 0 = (m + j) ∧
        f k = 1 ∧
        ∀ i : ℕ, i < k →
          f (i + 1) = (((Nat.digits 10 (f i)).map (fun d => d ^ 2)).sum)) →
    7899999999999959999999996 ≤ m := by
  constructor
  · intro j hj
    interval_cases j
    · exact HappySix.isHap_of_hapCert 10 (7899999999999959999999996 + 0)
        (by decide +kernel)
    · exact HappySix.isHap_of_hapCert 10 (7899999999999959999999996 + 1)
        (by decide +kernel)
    · exact HappySix.isHap_of_hapCert 10 (7899999999999959999999996 + 2)
        (by decide +kernel)
    · exact HappySix.isHap_of_hapCert 10 (7899999999999959999999996 + 3)
        (by decide +kernel)
    · exact HappySix.isHap_of_hapCert 10 (7899999999999959999999996 + 4)
        (by decide +kernel)
    · exact HappySix.isHap_of_hapCert 10 (7899999999999959999999996 + 5)
        (by decide +kernel)
  · intro m hm
    by_contra hcon
    have hlt : m < 7899999999999959999999996 := not_le.mp hcon
    have hN0lt : m < 10 ^ 25 := by
      have hN0 : 7899999999999959999999996 < 10 ^ 25 := by norm_num
      omega
    set q := m / 10 with hq_def
    set r := m % 10 with hr_def
    have hdm : 10 * q + r = m := by
      rw [hq_def, hr_def]
      exact Nat.div_add_mod m 10
    have hr10 : r < 10 := by
      rw [hr_def]
      exact Nat.mod_lt m (by norm_num)
    have hmlt : m < 10 * 10 ^ 24 := by
      have h25 : 10 * 10 ^ 24 = 10 ^ 25 := by rw [← Nat.pow_succ']
      omega
    have hq24 : q < 10 ^ 24 := by
      rw [hq_def]
      exact Nat.div_lt_of_lt_mul hmlt
    have hq1lt : q + 1 < 10 ^ 25 := by
      have h2425 : (10 : ℕ) ^ 24 < 10 ^ 25 := by norm_num
      omega
    have hSq : HappySix.digitSqSum q ≤ 2025 := by
      have hle := HappySix.digitSqSum_le_of_lt_pow 24 q hq24
      omega
    have hSq1 : HappySix.digitSqSum (q + 1) ≤ 2025 := by
      have hle := HappySix.digitSqSum_le_of_lt_pow 25 (q + 1) hq1lt
      omega
    have hallS : ∀ j : ℕ, j < 6 →
        HappySix.IsHap (HappySix.digitSqSum (m + j)) := by
      intro j hj
      obtain ⟨k, f, h0, hk, hstep⟩ := hm j hj
      have hhap : HappySix.IsHap (m + j) := ⟨k, f, h0, hk, hstep⟩
      exact HappySix.isHap_digitSqSum _ hhap
    have hall' : ∀ j : ℕ, j < 6 →
        HappySix.IsHap (HappySix.digitSqSum (10 * q + r + j)) := by
      intro j hj
      have e : m + j = 10 * q + r + j := by omega
      have hS := hallS j hj
      rw [e] at hS
      exact hS
    by_cases hr67 : r = 6 ∨ r = 7
    · have hle := HappySix.le_of_happy_run_residue_six_seven q r hr67 hSq hall'
      omega
    · have hr6 : r ≠ 6 := by omega
      have hr7 : r ≠ 7 := by omega
      exact HappySix.no_happy_run_of_residue q r hr10 hr6 hr7 hSq hSq1 hall'

end MetaMathlibExt
end
