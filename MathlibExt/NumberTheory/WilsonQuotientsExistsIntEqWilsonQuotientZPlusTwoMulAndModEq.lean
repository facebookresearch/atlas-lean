/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.WilsonQuotientsExistsNatEqWilsonQuotientZPlusIff
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.WilsonQuotients

/-!
# The sign-adjusted Wilson quotient sum at even arguments

For Morozov's sign-adjusted quotient sum `wilsonQuotientZPlus`, this module proves that `Z⁺(2n)`
is an integer congruent to `0` modulo `2n` for `n = 2` or non-prime `n ≠ 1`, and to `n + 1`
modulo `2n` for odd primes `n`.

Statements from Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", *INTEGERS* 25 (2025), Article A93.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.WilsonQuotientsWanted

private theorem distinct_mul_dvd_factorial (a b m : ℕ) (ha0 : 0 < a) (hb0 : 0 < b)
    (hne : a ≠ b) (ham : a ≤ m) (hbm : b ≤ m) : a * b ∣ m.factorial := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hale : a ≤ b - 1 := Nat.le_pred_of_lt hlt
    have hdvd : a ∣ (b - 1).factorial := Nat.dvd_factorial ha0 hale
    have hmul : a * b ∣ (b - 1).factorial * b := mul_dvd_mul_right hdvd b
    have hfact : (b - 1).factorial * b = b.factorial := by
      conv_rhs => rw [← Nat.sub_add_cancel hb0, Nat.factorial_succ, Nat.sub_add_cancel hb0]
      ac_rfl
    rw [hfact] at hmul
    exact hmul.trans (Nat.factorial_dvd_factorial hbm)
  · have hle : b ≤ a - 1 := Nat.le_pred_of_lt hgt
    have hdvd : b ∣ (a - 1).factorial := Nat.dvd_factorial hb0 hle
    have hmul : b * a ∣ (a - 1).factorial * a := mul_dvd_mul_right hdvd a
    have hfact : (a - 1).factorial * a = a.factorial := by
      conv_rhs => rw [← Nat.sub_add_cancel ha0, Nat.factorial_succ, Nat.sub_add_cancel ha0]
      ac_rfl
    rw [hfact] at hmul
    have hba : b * a ∣ m.factorial := hmul.trans (Nat.factorial_dvd_factorial ham)
    simpa [mul_comm b a] using hba

private theorem sum_factorial_pair_eq_two_mul (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (2 * n), ((Nat.factorial k * Nat.factorial (2 * n - 1 - k) : ℕ) : ℚ) =
      2 * ∑ k ∈ Finset.range n, ((Nat.factorial k * Nat.factorial (2 * n - 1 - k) : ℕ) : ℚ) := by
  let f : ℕ → ℚ := fun k => ((Nat.factorial k * Nat.factorial (2 * n - 1 - k) : ℕ) : ℚ)
  change ∑ k ∈ Finset.range (2 * n), f k = 2 * ∑ k ∈ Finset.range n, f k
  rw [two_mul, Finset.sum_range_add]
  have hmirror : ∀ k ∈ Finset.range n, f (n + k) = f (n - 1 - k) := by
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have h1 : 2 * n - 1 - (n + k) = n - 1 - k := by omega
    have h2 : 2 * n - 1 - (n - 1 - k) = n + k := by omega
    simp only [f, h1, h2]
    rw [mul_comm (Nat.factorial (n + k)) (Nat.factorial (n - 1 - k))]
  have hsum : ∑ k ∈ Finset.range n, f (n + k) = ∑ k ∈ Finset.range n, f k := by
    calc ∑ k ∈ Finset.range n, f (n + k) = ∑ k ∈ Finset.range n, f (n - 1 - k) :=
            Finset.sum_congr rfl hmirror
      _ = ∑ k ∈ Finset.range n, f k := Finset.sum_range_reflect f n
  rw [hsum]
  ring

private theorem wilsonQuotientZPlus_two_mul_eq_div (n : ℕ) (hn : 1 ≤ n) :
    wilsonQuotientZPlus (2 * n) =
      (∑ k ∈ Finset.range n, ((Nat.factorial k * Nat.factorial (2 * n - 1 - k) : ℕ) : ℚ)) / n := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have h2nR : ((2 * n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * n ≠ 0)
  have halt : ∑ k ∈ Finset.range (2 * n), (-1 : ℚ) ^ k = 0 := by
    rw [neg_one_geom_sum, ite_eq_left (even_two_mul n)]
  have hsub : ∀ k ∈ Finset.range (2 * n),
      Nat.factorial (2 * n - k - 1) = Nat.factorial (2 * n - 1 - k) := by
    intro k _
    rw [Nat.sub_right_comm]
  have hS : ∑ k ∈ Finset.range (2 * n),
        ((Nat.factorial k * Nat.factorial (2 * n - k - 1) : ℕ) : ℚ) =
      ∑ k ∈ Finset.range (2 * n), ((Nat.factorial k * Nat.factorial (2 * n - 1 - k) : ℕ) : ℚ) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsub k hk]
  have hsplit : wilsonQuotientZPlus (2 * n) =
      (∑ k ∈ Finset.range (2 * n), (-1 : ℚ) ^ k) / ((2 * n : ℕ) : ℚ) +
        (∑ k ∈ Finset.range (2 * n), ((Nat.factorial k * Nat.factorial (2 * n - k - 1) : ℕ) : ℚ)) /
          ((2 * n : ℕ) : ℚ) := by
    simp only [wilsonQuotientZPlus, wilsonQuotientMPlus, add_div]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [← Nat.cast_mul]
  rw [hsplit, halt, hS, sum_factorial_pair_eq_two_mul n hn]
  simp only [zero_div, zero_add]
  have hcast : ((2 * n : ℕ) : ℚ) = 2 * (n : ℚ) := by push_cast; ring
  rw [hcast]
  field_simp

private theorem dvd_quotient_term (n k : ℕ) (hn : 1 ≤ n) (hk : k < n) :
    n ∣ Nat.factorial k * Nat.factorial (2 * n - 1 - k) := by
  have hle : n ≤ 2 * n - 1 - k := by omega
  have hdvd : n ∣ Nat.factorial (2 * n - 1 - k) := Nat.dvd_factorial (by omega) hle
  exact hdvd.mul_left (Nat.factorial k)

private theorem sum_eq_mul_sum_div (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, Nat.factorial k * Nat.factorial (2 * n - 1 - k) =
      n * ∑ k ∈ Finset.range n, (Nat.factorial k * Nat.factorial (2 * n - 1 - k) / n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  exact (Nat.mul_div_cancel' (dvd_quotient_term n k hn hklt)).symm

private theorem wilsonQuotientZPlus_two_mul_eq_cast (n : ℕ) (hn : 1 ≤ n) :
    wilsonQuotientZPlus (2 * n) =
      ((∑ k ∈ Finset.range n, (Nat.factorial k * Nat.factorial (2 * n - 1 - k) / n) : ℕ) : ℚ) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  rw [wilsonQuotientZPlus_two_mul_eq_div n hn, ← Nat.cast_sum, sum_eq_mul_sum_div n hn]
  push_cast
  field_simp

private theorem quotient_eq_factorial_mul (n k : ℕ) (hn : 0 < n) (hk : k < n) :
    Nat.factorial k * Nat.factorial (2 * n - 1 - k) / n =
      Nat.factorial k * Nat.factorial (n - 1) * ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1)) := by
  have hadd : 2 * n - 1 - k = n + (n - 1 - k) := by omega
  have hprod : ∏ i ∈ Finset.range (n - 1 - k), (n + 1 + i) =
      ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1)) :=
    Finset.prod_congr rfl fun i _ => by rw [Nat.add_assoc, Nat.add_comm 1 i]
  rw [hadd, ← Nat.factorial_mul_ascFactorial n (n - 1 - k), Nat.ascFactorial_eq_prod_range,
    ← Nat.mul_factorial_pred hn.ne', hprod]
  have hcomm :
      Nat.factorial k *
          (n * Nat.factorial (n - 1) * ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1))) =
        n * (Nat.factorial k * Nat.factorial (n - 1) *
          ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1))) := by
    ac_rfl
  rw [hcomm, Nat.mul_div_cancel_left _ hn]

private theorem get_mul_pair_of_not_prime (n : ℕ) (hn : 1 ≤ n) (hnp : ¬(n = 1 ∨ n.Prime)) :
    ∃ a b : ℕ, n = a * b ∧ 2 ≤ a ∧ a < n ∧ 2 ≤ b ∧ b < n := by
  have hn1 : n ≠ 1 := fun h => hnp (Or.inl h)
  have hn2 : 2 ≤ n := by omega
  have hNotPrime : ¬n.Prime := fun h => hnp (Or.inr h)
  obtain ⟨m, hmdvd, hm2, hmlt⟩ := Nat.exists_dvd_of_not_prime2 hn2 hNotPrime
  obtain ⟨k, hk⟩ := hmdvd
  have hk1 : k ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hk
    omega
  have hkone : k ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hk
    omega
  have hk2 : 2 ≤ k := by omega
  have hklt : k < n := by
    have hkdvd : k ∣ n := ⟨m, by rw [hk, mul_comm]⟩
    have hkle : k ≤ n := Nat.le_of_dvd (by omega) hkdvd
    have hkne : k ≠ n := by
      intro heq
      rw [heq] at hk
      have hle : 2 * n ≤ m * n := Nat.mul_le_mul_right n hm2
      rw [← hk] at hle
      omega
    omega
  exact ⟨m, k, hk, hm2, hmlt, hk2, hklt⟩

private theorem two_mul_dvd_quotient_of_composite (n k : ℕ) (hn : 1 ≤ n)
    (hnp : ¬(n = 1 ∨ n.Prime)) (hn4 : n ≠ 4) (hk : k < n) :
    2 * n ∣ Nat.factorial k * Nat.factorial (2 * n - 1 - k) / n := by
  have hn0 : 0 < n := by omega
  rw [quotient_eq_factorial_mul n k hn0 hk]
  have hn1 : n ≠ 1 := fun h => hnp (Or.inl h)
  have hn2 : n ≠ 2 := by
    intro h2
    apply hnp
    right
    rw [h2]
    exact Nat.prime_two
  have hn3 : n ≠ 3 := by
    intro h3
    apply hnp
    right
    rw [h3]
    exact Nat.prime_three
  have hn5 : 5 ≤ n := by omega
  obtain ⟨a, b, hab, ha2, halt, hb2, hblt⟩ := get_mul_pair_of_not_prime n hn hnp
  by_cases heq : a = b
  · have ha3 : 3 ≤ a := by
      have hane2 : a ≠ 2 := by
        intro ha2eq
        rw [ha2eq] at heq
        have hn44 : n = 4 := by rw [hab, ha2eq, ← heq]
        exact hn4 hn44
      omega
    have h2ale : 2 * a ≤ n - 1 := by
      have hmul : 3 * a ≤ a * a := Nat.mul_le_mul_right a ha3
      have hab2 : n = a * a := by rw [hab, heq]
      omega
    have hane : a ≠ 2 * a := by omega
    have ham : a ≤ n - 1 := by omega
    have h2am : 2 * a ≤ n - 1 := h2ale
    have hdvd : a * (2 * a) ∣ (n - 1).factorial :=
      distinct_mul_dvd_factorial a (2 * a) (n - 1) (by omega) (by omega) hane ham h2am
    have h2n : 2 * n = a * (2 * a) := by
      rw [hab, heq]
      ring
    rw [h2n] at *
    obtain ⟨t, ht⟩ := hdvd
    have hq :
        Nat.factorial k * Nat.factorial (n - 1) * ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1)) =
          (a * (2 * a)) *
            (Nat.factorial k * t * ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1))) := by
      rw [ht]
      ac_rfl
    rw [hq]
    exact Nat.dvd_mul_right _ _
  · have hdiv : n ∣ (n - 1).factorial := by
      have ham : a ≤ n - 1 := by omega
      have hbm : b ≤ n - 1 := by omega
      have hdvd : a * b ∣ (n - 1).factorial :=
        distinct_mul_dvd_factorial a b (n - 1) (by omega) (by omega) heq ham hbm
      rwa [← hab] at hdvd
    obtain ⟨t, ht⟩ := hdiv
    have h2dvd : 2 ∣ Nat.factorial k * t * ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1)) := by
      by_cases hk2 : 2 ≤ k
      · have h2k : 2 ∣ Nat.factorial k := Nat.dvd_factorial (by norm_num) hk2
        have hmul : 2 ∣ Nat.factorial k * (t * ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1))) :=
          h2k.mul_right _
        simpa [mul_assoc] using hmul
      · have hj2 : 2 ≤ n - 1 - k := by omega
        have h0mem : 0 ∈ Finset.range (n - 1 - k) := Finset.mem_range.mpr (by omega)
        have h1mem : 1 ∈ Finset.range (n - 1 - k) := Finset.mem_range.mpr (by omega)
        have hdvd1 : n + (0 + 1) ∣ ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1)) :=
          Finset.dvd_prod_of_mem _ h0mem
        have hdvd2 : n + (1 + 1) ∣ ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1)) :=
          Finset.dvd_prod_of_mem _ h1mem
        have hor : 2 ∣ n + (0 + 1) ∨ 2 ∣ n + (1 + 1) := by omega
        have h2R : 2 ∣ ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1)) := by
          rcases hor with hL | hR
          · exact hL.trans hdvd1
          · exact hR.trans hdvd2
        exact h2R.mul_left _
    obtain ⟨s, hs⟩ := h2dvd
    refine ⟨s, ?_⟩
    calc Nat.factorial k * Nat.factorial (n - 1) * ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1))
        = Nat.factorial k * (n * t) * ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1)) := by rw [ht]
      _ = n * (Nat.factorial k * t * ∏ i ∈ Finset.range (n - 1 - k), (n + (i + 1))) := by ac_rfl
      _ = n * (2 * s) := by rw [hs]
      _ = 2 * n * s := by ac_rfl

private theorem two_dvd_quotient_of_odd_prime (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : k < p) :
    2 ∣ Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p := by
  have hp2le : 2 ≤ p := hp.two_le
  have hp3 : 3 ≤ p := by omega
  have hpMod : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hpOdd : Odd p := Nat.odd_iff.mpr hpMod
  have hCop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpOdd
  have h2le : 2 ≤ 2 * p - 1 - k := by omega
  have hple : p ≤ 2 * p - 1 - k := by omega
  have h2dvd : 2 ∣ Nat.factorial (2 * p - 1 - k) := Nat.dvd_factorial (by norm_num) h2le
  have hpdvd : p ∣ Nat.factorial (2 * p - 1 - k) := Nat.dvd_factorial hp.pos hple
  have h2p : 2 * p ∣ Nat.factorial (2 * p - 1 - k) := hCop.mul_dvd_of_dvd_of_dvd h2dvd hpdvd
  have h2pX : 2 * p ∣ Nat.factorial k * Nat.factorial (2 * p - 1 - k) := h2p.mul_left _
  obtain ⟨t, ht⟩ := h2pX
  have hrewrite : 2 * p * t = p * (2 * t) := by ac_rfl
  have hEq : Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p = 2 * t := by
    rw [ht, hrewrite, Nat.mul_div_cancel_left _ hp.pos]
  rw [hEq]
  exact Nat.dvd_mul_right 2 t

private theorem quotient_modEq_pow_of_odd_prime (p k : ℕ) (hp : p.Prime) (hk : k < p) :
    ((Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p : ℕ) : ℤ) ≡
      (-1 : ℤ) ^ k [ZMOD (p : ℤ)] := by
  have hppos : 0 < p := hp.pos
  have hn1 : 1 ≤ p := by omega
  have hYeq : Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p =
      Nat.factorial k * Nat.factorial (p - 1) * ∏ i ∈ Finset.range (p - 1 - k), (p + (i + 1)) :=
    quotient_eq_factorial_mul p k hppos hk
  have hR : ((∏ i ∈ Finset.range (p - 1 - k), (p + (i + 1)) : ℕ) : ZMod p) =
      ((Nat.factorial (p - 1 - k) : ℕ) : ZMod p) := by
    rw [Nat.cast_prod]
    have hfac : ∀ i ∈ Finset.range (p - 1 - k),
        ((p + (i + 1) : ℕ) : ZMod p) = ((i + 1 : ℕ) : ZMod p) := by
      intro i _
      simp only [Nat.cast_add, ZMod.natCast_self, zero_add]
    rw [Finset.prod_congr rfl hfac, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  have hFact : Fact p.Prime := ⟨hp⟩
  have hWilson : ((Nat.factorial (p - 1) : ℕ) : ZMod p) = -1 := @ZMod.wilsons_lemma p hFact
  have hIff := neg_one_pow_mul_factorial_mul_factorial_modEq_neg_one_iff p k hn1 hk
  have hMod :
      (-1 : ℤ) ^ k * (Nat.factorial k * Nat.factorial (p - k - 1) : ℤ) ≡ -1 [ZMOD (p : ℤ)] :=
    hIff.mpr (Or.inr hp)
  have hsub : p - k - 1 = p - 1 - k := Nat.sub_right_comm p k 1
  rw [hsub] at hMod
  have hZMod : (-1 : ZMod p) ^ k *
      (((Nat.factorial k : ℕ) : ZMod p) * ((Nat.factorial (p - 1 - k) : ℕ) : ZMod p)) = -1 := by
    have hcast := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hMod
    simpa using hcast
  have he2 : (-1 : ZMod p) ^ k * (-1 : ZMod p) ^ k = 1 := by
    rw [← pow_add]
    have heven : Even (k + k) := ⟨k, by ring⟩
    exact heven.neg_one_pow
  have ha : ((Nat.factorial k : ℕ) : ZMod p) * ((Nat.factorial (p - 1 - k) : ℕ) : ZMod p) =
      -((-1 : ZMod p) ^ k) := by
    have h1 := congrArg (fun x : ZMod p => (-1 : ZMod p) ^ k * x) hZMod
    simpa [← mul_assoc, he2, one_mul] using h1
  have hY :
      ((Nat.factorial k * Nat.factorial (p - 1) *
          ∏ i ∈ Finset.range (p - 1 - k), (p + (i + 1)) : ℕ) : ZMod p) =
        (-1 : ZMod p) ^ k := by
    have hcast :
        ((Nat.factorial k * Nat.factorial (p - 1) *
            ∏ i ∈ Finset.range (p - 1 - k), (p + (i + 1)) : ℕ) : ZMod p) =
          ((Nat.factorial k : ℕ) : ZMod p) * ((Nat.factorial (p - 1) : ℕ) : ZMod p) *
            ((∏ i ∈ Finset.range (p - 1 - k), (p + (i + 1)) : ℕ) : ZMod p) := by
      push_cast
      ring
    rw [hcast, hWilson, hR]
    have hneg : ((Nat.factorial k : ℕ) : ZMod p) * -1 * ((Nat.factorial (p - 1 - k) : ℕ) : ZMod p) =
        -(((Nat.factorial k : ℕ) : ZMod p) * ((Nat.factorial (p - 1 - k) : ℕ) : ZMod p)) := by
      ring
    rw [hneg, ha, neg_neg]
  have hYcast0 : (((Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p : ℕ) : ℤ) : ZMod p) =
      (-1 : ZMod p) ^ k := by
    rw [hYeq]
    have hNat :
        (((Nat.factorial k * Nat.factorial (p - 1) *
            ∏ i ∈ Finset.range (p - 1 - k), (p + (i + 1)) : ℕ) : ℤ) : ZMod p) =
          ((Nat.factorial k * Nat.factorial (p - 1) *
            ∏ i ∈ Finset.range (p - 1 - k), (p + (i + 1)) : ℕ) : ZMod p) := by
      simp
    rw [hNat, hY]
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  simpa using hYcast0

private theorem modEq_two_mul_of_odd (p : ℕ) (x e : ℤ) (hxEven : Even x) (heOdd : Odd e)
    (hmod : x ≡ e [ZMOD (p : ℤ)]) : x ≡ (p : ℤ) + e [ZMOD 2 * (p : ℤ)] := by
  have hDvd : (p : ℤ) ∣ e - x := Int.modEq_iff_dvd.mp hmod
  obtain ⟨t, ht⟩ := hDvd
  have hxsub : x - e = (p : ℤ) * (-t) := by
    have h1 : x - e = -(e - x) := by ring
    rw [h1, ht]
    ring
  have hOddSub : Odd (x - e) := hxEven.sub_odd heOdd
  rw [hxsub] at hOddSub
  have hOddNeg : Odd (-t) := (Int.odd_mul.mp hOddSub).2
  obtain ⟨r, hr⟩ := hOddNeg
  have hEq : ((p : ℤ) + e) - x = (2 * (p : ℤ)) * (-r) := by
    have h1 : ((p : ℤ) + e) - x = (p : ℤ) - (x - e) := by ring
    rw [h1, hxsub, hr]
    ring
  exact Int.modEq_iff_dvd.mpr ⟨-r, hEq⟩

private theorem quotient_modEq_add_pow_of_odd_prime (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : k < p) :
    ((Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p : ℕ) : ℤ) ≡
      (p : ℤ) + (-1 : ℤ) ^ k [ZMOD 2 * (p : ℤ)] := by
  have h2dvd : 2 ∣ Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p :=
    two_dvd_quotient_of_odd_prime p k hp hp2 hk
  obtain ⟨r, hr⟩ := h2dvd
  have hxEven : Even (((Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p : ℕ) : ℤ)) := by
    refine ⟨(r : ℤ), ?_⟩
    rw [hr]
    push_cast
    ring
  have heOdd : Odd ((-1 : ℤ) ^ k) := odd_neg_one.pow
  have hmod : ((Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p : ℕ) : ℤ) ≡
      (-1 : ℤ) ^ k [ZMOD (p : ℤ)] := quotient_modEq_pow_of_odd_prime p k hp hk
  exact modEq_two_mul_of_odd p _ _ hxEven heOdd hmod

private theorem sq_modEq_self_of_odd (p : ℕ) (hodd : Odd p) :
    (p : ℤ) ^ 2 ≡ (p : ℤ) [ZMOD 2 * (p : ℤ)] := by
  obtain ⟨m, hm⟩ := hodd
  have hcast : (p : ℤ) = 2 * (m : ℤ) + 1 := by
    rw [hm]
    push_cast
    ring
  have hEq : (p : ℤ) - (p : ℤ) ^ 2 = (2 * (p : ℤ)) * (-(m : ℤ)) := by
    rw [hcast]
    ring
  exact Int.modEq_iff_dvd.mpr ⟨-(m : ℤ), hEq⟩

private theorem sum_add_pow_eq_sq_add_one (p : ℕ) (hodd : Odd p) :
    ∑ k ∈ Finset.range p, ((p : ℤ) + (-1 : ℤ) ^ k) = (p : ℤ) ^ 2 + 1 := by
  rw [Finset.sum_add_distrib]
  have hsumP : ∑ k ∈ Finset.range p, (p : ℤ) = (p : ℤ) ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two]
  have hsumA : ∑ k ∈ Finset.range p, (-1 : ℤ) ^ k = 1 := by
    rw [neg_one_geom_sum, ite_eq_right (Nat.not_even_iff_odd.mpr hodd)]
  rw [hsumP, hsumA]

private theorem sum_quotient_modEq_zero_of_composite (n : ℕ) (hn : 1 ≤ n)
    (hnp : ¬(n = 1 ∨ n.Prime)) (hn4 : n ≠ 4) :
    ∑ k ∈ Finset.range n, (((Nat.factorial k * Nat.factorial (2 * n - 1 - k) / n : ℕ) : ℤ)) ≡
      0 [ZMOD 2 * (n : ℤ)] := by
  apply Int.ModEq.sum_zero
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  have hdiv : 2 * n ∣ Nat.factorial k * Nat.factorial (2 * n - 1 - k) / n :=
    two_mul_dvd_quotient_of_composite n k hn hnp hn4 hklt
  obtain ⟨c, hc⟩ := hdiv
  have hEq : (((Nat.factorial k * Nat.factorial (2 * n - 1 - k) / n : ℕ) : ℤ)) =
      (2 * (n : ℤ)) * ((c : ℕ) : ℤ) := by
    rw [hc]
    push_cast
    ring
  exact Int.modEq_zero_iff_dvd.mpr ⟨(c : ℤ), hEq⟩

private theorem sum_quotient_modEq_add_one_of_odd_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ k ∈ Finset.range p, (((Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p : ℕ) : ℤ)) ≡
      (p : ℤ) + 1 [ZMOD 2 * (p : ℤ)] := by
  have hpMod : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hpOdd : Odd p := Nat.odd_iff.mpr hpMod
  have hsum :
      ∑ k ∈ Finset.range p, (((Nat.factorial k * Nat.factorial (2 * p - 1 - k) / p : ℕ) : ℤ)) ≡
        ∑ k ∈ Finset.range p, ((p : ℤ) + (-1 : ℤ) ^ k) [ZMOD 2 * (p : ℤ)] := by
    apply Int.ModEq.sum
    intro k hk
    have hklt : k < p := Finset.mem_range.mp hk
    exact quotient_modEq_add_pow_of_odd_prime p k hp hp2 hklt
  have hEq : ∑ k ∈ Finset.range p, ((p : ℤ) + (-1 : ℤ) ^ k) = (p : ℤ) ^ 2 + 1 :=
    sum_add_pow_eq_sq_add_one p hpOdd
  rw [hEq] at hsum
  have hsq : (p : ℤ) ^ 2 ≡ (p : ℤ) [ZMOD 2 * (p : ℤ)] := sq_modEq_self_of_odd p hpOdd
  have hsq1 : (p : ℤ) ^ 2 + 1 ≡ (p : ℤ) + 1 [ZMOD 2 * (p : ℤ)] := hsq.add_right 1
  exact hsum.trans hsq1

/-- **The sign-adjusted Wilson quotient sum Z⁺(2n) modulo 2n.** Let $n \ge 1$ be a natural
number. Morozov's sign-adjusted Wilson quotient sum $Z^+(2n)$ is an integer; it satisfies
$Z^+(2n) \equiv 0 \pmod{2n}$ if $n = 2$ or $n$ is neither $1$ nor prime, and
$Z^+(2n) \equiv n + 1 \pmod{2n}$ if $n$ is an odd prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 5, equations (8) and (9). -/
theorem exists_int_eq_wilsonQuotientZPlus_two_mul_and_modEq
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZPlus (2 * n) ∧
      (((n = 2 ∨ ¬(n = 1 ∨ n.Prime)) → z ≡ 0 [ZMOD (2 * n : ℤ)]) ∧
        (((n.Prime ∧ n ≠ 2) → z ≡ (n : ℤ) + 1 [ZMOD (2 * n : ℤ)]))) := by
  refine ⟨((∑ k ∈ Finset.range n, (Nat.factorial k * Nat.factorial (2 * n - 1 - k) / n) : ℕ) : ℤ),
    ?_, ?_, ?_⟩
  · have hcast := wilsonQuotientZPlus_two_mul_eq_cast n hn
    rw [hcast]
    exact Int.cast_natCast _
  · intro h
    rcases h with rfl | hcomp
    · decide
    · by_cases hn4 : n = 4
      · subst hn4
        decide
      · have hsum := sum_quotient_modEq_zero_of_composite n hn hcomp hn4
        rw [Nat.cast_sum]
        exact hsum
  · intro h
    obtain ⟨hp, hp2⟩ := h
    have hsum := sum_quotient_modEq_add_one_of_odd_prime n hp hp2
    rw [Nat.cast_sum]
    exact hsum

end MathlibExt.NumberTheory.WilsonQuotientsWanted
