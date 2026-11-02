/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace MetaMathlibExt

/-! # Sylvester coin theorem for distinct odd primes
-/

private lemma res_ex (p q n : ℕ) (hcop : Nat.Coprime p q) (hq : 2 ≤ q) :
    ∃ i, i < q ∧ (p * i) % q = n % q := by
  have hq0 : 0 < q := by omega
  have hinj : ∀ a b : ℕ, a < q → b < q → (p * a) % q = (p * b) % q → a = b := by
    intro a b ha hb h
    have hmod : p * a ≡ p * b [MOD q] := h
    have hcan : a ≡ b [MOD q] :=
      Nat.ModEq.cancel_left_of_coprime hcop.symm hmod
    exact Nat.ModEq.eq_of_lt_of_lt hcan ha hb
  have hinjOn : Set.InjOn (fun i => (p * i) % q) ↑(Finset.range q) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    exact hinj a b ha hb (by simpa using hab)
  have hcard : ((Finset.range q).image (fun i => (p * i) % q)).card = q := by
    rw [Finset.card_image_of_injOn hinjOn, Finset.card_range]
  have heq : (Finset.range q).image (fun i => (p * i) % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_range.mpr (Nat.mod_lt _ hq0)
    · rw [hcard, Finset.card_range]
  have hmem : n % q ∈ (Finset.range q).image (fun i => (p * i) % q) := by
    rw [heq]
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq0)
  obtain ⟨i, hi, hif⟩ := Finset.mem_image.mp hmem
  exact ⟨i, Finset.mem_range.mp hi, hif⟩

private lemma repr_iff (p q n : ℕ) (hq : 2 ≤ q) :
    (∃ x y : ℕ, n = p * x + q * y) ↔
      ∃ i, i < q ∧ p * i ≤ n ∧ (n - p * i) % q = 0 := by
  constructor
  · rintro ⟨x, y, rfl⟩
    refine ⟨x % q, Nat.mod_lt _ (by omega), ?_, ?_⟩
    · have hle : p * (x % q) ≤ p * x :=
        Nat.mul_le_mul (le_refl p) (Nat.mod_le x q)
      omega
    · have hdm : q * (x / q) + x % q = x := Nat.div_add_mod x q
      have e1 : p * x = p * (x % q) + q * (p * (x / q)) := by
        conv_lhs => rw [← hdm]
        ring
      have e2 : q * (p * (x / q) + y) = q * (p * (x / q)) + q * y := by ring
      have hsub : p * x + q * y - p * (x % q) = q * (p * (x / q) + y) := by omega
      rw [hsub]
      exact Nat.mul_mod_right q _
  · rintro ⟨i, -, hle, hmod⟩
    refine ⟨i, (n - p * i) / q, ?_⟩
    have hdm : q * ((n - p * i) / q) + (n - p * i) % q = n - p * i :=
      Nat.div_add_mod _ _
    rw [hmod] at hdm
    omega

private lemma mul_pred_eq (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    p * (q - 1) = p * q - p := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have e : (a + 1) * (b + 1) = (a + 1) * b + (a + 1) := by ring
  omega

private lemma repr_large (p q n : ℕ) (hcop : Nat.Coprime p q) (hq : 2 ≤ q) (hp : 2 ≤ p)
    (hN : p * q - p - q + 1 ≤ n) : ∃ x y : ℕ, n = p * x + q * y := by
  obtain ⟨i, hiq, hmod⟩ := res_ex p q n hcop hq
  have hle : p * i ≤ n := by
    by_contra hcon
    have hlt : n < p * i := lt_of_not_ge hcon
    have hdvd : q ∣ (p * i - n) := (Nat.modEq_iff_dvd' hlt.le).mp hmod.symm
    have hpos : 0 < p * i - n := by omega
    have hqle : q ≤ p * i - n := Nat.le_of_dvd hpos hdvd
    have hmul : p * i ≤ p * (q - 1) :=
      Nat.mul_le_mul (le_refl p) (by omega : i ≤ q - 1)
    have hpq := mul_pred_eq p q (by omega) (by omega)
    omega
  rw [repr_iff p q n hq]
  exact ⟨i, hiq, hle, Nat.mod_eq_zero_of_dvd ((Nat.modEq_iff_dvd' hle).mp hmod)⟩

private lemma not_both (p q n m : ℕ) (hcop : Nat.Coprime p q) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hsum : n + m + p + q = p * q)
    (hn : ∃ x y : ℕ, n = p * x + q * y)
    (hm : ∃ x y : ℕ, m = p * x + q * y) : False := by
  obtain ⟨x1, y1, r1⟩ := hn
  obtain ⟨x2, y2, r2⟩ := hm
  have e : p * (x1 + x2 + 1) + q * (y1 + y2 + 1) = p * q := by
    have d1 : p * (x1 + x2 + 1) = p * x1 + p * x2 + p := by ring
    have d2 : q * (y1 + y2 + 1) = q * y1 + q * y2 + q := by ring
    omega
  have hqX : q ∣ p * (x1 + x2 + 1) := by
    have h1 : q ∣ p * (x1 + x2 + 1) + q * (y1 + y2 + 1) := by
      rw [e]
      exact ⟨p, by ring⟩
    have h2 : (p * (x1 + x2 + 1) + q * (y1 + y2 + 1)) % q
        = (p * (x1 + x2 + 1)) % q :=
      Nat.add_mul_mod_self_left _ _ _
    rw [Nat.mod_eq_zero_of_dvd h1] at h2
    exact Nat.dvd_of_mod_eq_zero h2.symm
  have hpY : p ∣ q * (y1 + y2 + 1) := by
    have h1 : p ∣ p * (x1 + x2 + 1) + q * (y1 + y2 + 1) := by
      rw [e]
      exact ⟨q, by ring⟩
    have h2 : (q * (y1 + y2 + 1) + p * (x1 + x2 + 1)) % p
        = (q * (y1 + y2 + 1)) % p :=
      Nat.add_mul_mod_self_left _ _ _
    have h3 : (p * (x1 + x2 + 1) + q * (y1 + y2 + 1)) % p = 0 :=
      Nat.mod_eq_zero_of_dvd h1
    rw [Nat.add_comm] at h3
    rw [h3] at h2
    exact Nat.dvd_of_mod_eq_zero h2.symm
  have hX : q ≤ x1 + x2 + 1 :=
    Nat.le_of_dvd (by omega) (hcop.symm.dvd_of_dvd_mul_left hqX)
  have hY : p ≤ y1 + y2 + 1 :=
    Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_left hpY)
  have g1 : p * q ≤ p * (x1 + x2 + 1) := Nat.mul_le_mul (le_refl p) hX
  have g2 : q * p ≤ q * (y1 + y2 + 1) := Nat.mul_le_mul (le_refl q) hY
  have hpos : 0 < q * p := Nat.mul_pos (by omega) (by omega)
  omega

private lemma one_of (p q n m : ℕ) (hcop : Nat.Coprime p q) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hsum : n + m + p + q = p * q) :
    (∃ x y : ℕ, n = p * x + q * y) ∨ ∃ x y : ℕ, m = p * x + q * y := by
  obtain ⟨i, hiq, hmod⟩ := res_ex p q n hcop hq
  by_cases hle : p * i ≤ n
  · left
    rw [repr_iff p q n hq]
    exact ⟨i, hiq, hle, Nat.mod_eq_zero_of_dvd ((Nat.modEq_iff_dvd' hle).mp hmod)⟩
  · right
    have hlt : n < p * i := lt_of_not_ge hle
    have hdvd : q ∣ (p * i - n) := (Nat.modEq_iff_dvd' hlt.le).mp hmod.symm
    have hpos : 0 < p * i - n := by omega
    have hqle : q ≤ p * i - n := Nat.le_of_dvd hpos hdvd
    have hiq1 : i ≤ q - 1 := by omega
    have hmul : p * i ≤ p * (q - 1) := Nat.mul_le_mul (le_refl p) hiq1
    have hpq := mul_pred_eq p q (by omega) (by omega)
    have eadd : p * (q - 1 - i) + p * i = p * (q - 1) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have e1 : p * (q - 1 - i) = p * q - p - p * i := by omega
    have hmX : p * (q - 1 - i) ≤ m := by omega
    have e2 : m - p * (q - 1 - i) = (p * i - n) - q := by omega
    rw [repr_iff p q m hq]
    refine ⟨q - 1 - i, by omega, hmX, ?_⟩
    rw [e2]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hdvd (dvd_refl q))

/--
**Sylvester's coin theorem for two distinct odd primes.** Let $p$ and $q$ be distinct odd
primes. Then the number of natural numbers $n$ that cannot be written as $n = px + qy$ with
natural numbers $x, y$ is $(p-1)(q-1)/2$.

Distinct odd primes are coprime, so this is a special case of Sylvester's count for coprime
$p$ and $q$.

Source: Damanvir Singh Binner, "Generalization of a Result of Sylvester
Related to the Frobenius Coin Problem", Journal of Integer Sequences 24 (2021),
Article 21.8.4, Theorem `Sylvester'` (the Special Case of Sylvester's theorem),
source lines 123–127,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Binner/binner13.tex>.
The paper attributes the general coprime statement to Sylvester (1882).
-/
theorem sylvester_coin_distinct_odd_primes
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hodd : Odd p ∧ Odd q) (hne : p ≠ q) :
    Nat.card { n : ℕ // ¬ ∃ x y : ℕ, n = p * x + q * y }
      = (p - 1) * (q - 1) / 2 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hpm := Nat.odd_iff.mp hodd.1
  have hqm := Nat.odd_iff.mp hodd.2
  have hp3 : 3 ≤ p := by omega
  have hq3 : 3 ≤ q := by omega
  have e23 : ∀ a b : ℕ, (a + 1) * (b + 1) = a * b + a + b + 1 := fun a b => by ring
  have h1 : p - 1 + 1 = p := by omega
  have h2 : q - 1 + 1 = q := by omega
  have e2 := e23 (p - 1) (q - 1)
  rw [h1, h2] at e2
  have hA1 : 1 ≤ (p - 1) * (q - 1) := by
    have h := Nat.mul_le_mul (by omega : 1 ≤ p - 1) (by omega : 1 ≤ q - 1)
    simpa using h
  have hle : p + q ≤ p * q := by omega
  set N := p * q - p - q with hN
  have hNpq : N + p + q = p * q := by omega
  have hNp1 : N + 1 = (p - 1) * (q - 1) := by omega
  classical
  set A := (Finset.range (N + 1)).filter
    (fun n => ∃ x y : ℕ, n = p * x + q * y) with hA
  set B := (Finset.range (N + 1)).filter
    (fun n => ¬ ∃ x y : ℕ, n = p * x + q * y) with hB
  have hcardS : Nat.card { n : ℕ // ¬ ∃ x y : ℕ, n = p * x + q * y } = B.card := by
    have h1c : Nat.card { n : ℕ // ¬ ∃ x y : ℕ, n = p * x + q * y } =
        ({n : ℕ | ¬ ∃ x y : ℕ, n = p * x + q * y}).ncard :=
      Nat.card_coe_set_eq _
    rw [h1c]
    have h2c : ({n : ℕ | ¬ ∃ x y : ℕ, n = p * x + q * y} : Set ℕ) = ↑B := by
      ext n
      simp only [Set.mem_ofPred_eq, hB, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · intro hn
        by_cases hmem : n < N + 1
        · exact ⟨hmem, hn⟩
        · exfalso
          have hge : N + 1 ≤ n := by omega
          exact hn (repr_large p q n hcop hq2 hp2 (by omega))
      · rintro ⟨-, hn⟩
        exact hn
    rw [h2c, Set.ncard_coe_finset]
  have hsum_cards : A.card + B.card = N + 1 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.range (N + 1))
      (fun n => ∃ x y : ℕ, n = p * x + q * y)
    rw [Finset.card_range] at h
    rw [hA, hB]
    exact h
  have hbij : A.card = B.card := by
    apply Finset.card_bij (fun n _ => N - n)
    · intro n hn
      rw [hA] at hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hnr, hnR⟩ := hn
      rw [hB]
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      intro hcon
      have hsum : n + (N - n) + p + q = p * q := by omega
      exact not_both p q n (N - n) hcop hp2 hq2 hsum hnR hcon
    · intro a ha b hb hab
      have hab2 : N - a = N - b := hab
      rw [hA] at ha hb
      simp only [Finset.mem_filter, Finset.mem_range] at ha hb
      omega
    · intro m hm
      rw [hB] at hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      obtain ⟨hmr, hmR⟩ := hm
      refine ⟨N - m, ?_, by omega⟩
      · rw [hA]
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have hsum : (N - m) + m + p + q = p * q := by omega
        rcases one_of p q (N - m) m hcop hp2 hq2 hsum with h | h
        · exact h
        · exact absurd h hmR
  have hfin : B.card = (N + 1) / 2 := by omega
  rw [hcardS, hfin, hNp1]

end MetaMathlibExt
