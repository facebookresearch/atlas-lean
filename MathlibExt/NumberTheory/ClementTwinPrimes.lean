/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- Forward direction of Clement's criterion, reindexed with `p = k + 1`
(so `p - 1 = k` and `p + 2 = k + 3`, avoiding natural subtraction).

Given `Nat.Prime (k + 1)` and `Nat.Prime (k + 3)`, Wilson's theorem gives
`(k ! : ZMod (k+1)) = -1` and `((k+2)! : ZMod (k+3)) = -1`; expanding
`(k+2)! = (k+2) * ((k+1) * k!)` and evaluating `k + 2 = -1`,
`k + 1 = -2` in `ZMod (k + 3)` yields divisibility by each factor, which
combine by coprimality. -/
private theorem clement_aux_forward (k : ℕ) (hk : 4 ≤ k) (hp : Nat.Prime (k + 1))
    (hq : Nat.Prime (k + 3)) :
    (k + 1) * (k + 3) ∣ 4 * (Nat.factorial k + 1) + (k + 1) := by
  have hdvd1 : (k + 1) ∣ (Nat.factorial k + 1) := by
    have W : ((Nat.factorial (k + 1 - 1) : ℕ) : ZMod (k + 1)) = -1 :=
      @ZMod.wilsons_lemma (k + 1) ⟨hp⟩
    rw [Nat.add_sub_cancel] at W
    have h0 : ((Nat.factorial k + 1 : ℕ) : ZMod (k + 1)) = 0 := by
      push_cast
      rw [W]
      ring
    exact (CharP.cast_eq_zero_iff (ZMod (k + 1)) (k + 1) _).mp h0
  have h1 : (k + 1) ∣ 4 * (Nat.factorial k + 1) + (k + 1) :=
    dvd_add (dvd_mul_of_dvd_right hdvd1 4) (dvd_refl _)
  have h2 : (k + 3) ∣ 4 * (Nat.factorial k + 1) + (k + 1) := by
    have hW := @ZMod.wilsons_lemma (k + 3) ⟨hq⟩
    have F : Nat.factorial (k + 2) = (k + 2) * ((k + 1) * Nat.factorial k) := by
      rw [show k + 2 = (k + 1) + 1 from by ring, Nat.factorial_succ,
        Nat.factorial_succ]
    rw [show k + 3 - 1 = k + 2 from by omega, F, Nat.cast_mul,
      Nat.cast_mul] at hW
    have h1' : ((k + 2 : ℕ) : ZMod (k + 3)) = -1 := by
      have hz : ((k + 3 : ℕ) : ZMod (k + 3)) = 0 := ZMod.natCast_self _
      have hcast : ((k + 2 : ℕ) : ZMod (k + 3)) + 1
          = ((k + 3 : ℕ) : ZMod (k + 3)) := by
        simp only [Nat.cast_add, Nat.cast_ofNat]
        ring
      linear_combination hcast + hz
    have h2' : ((k + 1 : ℕ) : ZMod (k + 3)) = -2 := by
      have hcast : ((k + 1 : ℕ) : ZMod (k + 3)) + 1
          = ((k + 2 : ℕ) : ZMod (k + 3)) := by
        simp only [Nat.cast_add, Nat.cast_ofNat]
        ring
      linear_combination hcast + h1'
    rw [h1', h2'] at hW
    have hF : (2 : ZMod (k + 3)) * ((Nat.factorial k : ℕ) : ZMod (k + 3))
        + 1 = 0 := by
      linear_combination hW
    have hdvd2 : (k + 3) ∣ (2 * Nat.factorial k + 1) :=
      (CharP.cast_eq_zero_iff (ZMod (k + 3)) (k + 3) _).mp (by
        push_cast
        linear_combination hF)
    have hXeq : 4 * (Nat.factorial k + 1) + (k + 1)
        = 2 * (2 * Nat.factorial k + 1) + (k + 3) := by ring
    rw [hXeq]
    exact dvd_add (dvd_mul_of_dvd_right hdvd2 2) (dvd_refl _)
  have hcop : Nat.Coprime (k + 1) (k + 3) := by
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have hsub := Nat.dvd_sub hd (dvd_refl (k + 1))
    rw [show k + 3 - (k + 1) = 2 from by omega] at hsub
    have hle := Nat.le_of_dvd (by norm_num) hsub
    omega
  exact hcop.mul_dvd_of_dvd_of_dvd h1 h2

/-- Backward direction of Clement's criterion, reindexed with `p = k + 1`.

From `(k+1) * (k+3) ∣ 4 * (k! + 1) + (k+1)` we get
`(k+1) ∣ 4 * (k!+1)` and `(k+3) ∣ 4 * k! + 2`. An even `k + 1 ≥ 4` is
impossible (else `(k+3)/2 ≤ k` divides both `4 * k!` and `4 * k! + 2`,
hence divides `2`). Otherwise any prime divisor `m = minFac` of `k + 1`
(resp. `k + 3`) is `≤ k`, hence divides `k!`, hence divides `4`
(resp. `2`), forcing `m = 2`, contradicting oddness. -/
private theorem clement_aux_backward (k : ℕ) (hk : 4 ≤ k)
    (h : (k + 1) * (k + 3) ∣ 4 * (Nat.factorial k + 1) + (k + 1)) :
    Nat.Prime (k + 1) ∧ Nat.Prime (k + 3) := by
  have h1 : (k + 1) ∣ 4 * (Nat.factorial k + 1) + (k + 1) :=
    dvd_trans (Nat.dvd_mul_right _ _) h
  have h3 : (k + 3) ∣ 4 * (Nat.factorial k + 1) + (k + 1) :=
    dvd_trans (Nat.dvd_mul_left _ _) h
  have g1 : (k + 1) ∣ 4 * (Nat.factorial k + 1) :=
    (Nat.dvd_add_left (dvd_refl _)).mp h1
  have hXeq : 4 * (Nat.factorial k + 1) + (k + 1)
      = (4 * Nat.factorial k + 2) + (k + 3) := by ring
  have g3 : (k + 3) ∣ 4 * Nat.factorial k + 2 := by
    rw [hXeq] at h3
    exact (Nat.dvd_add_left (dvd_refl _)).mp h3
  have hodd1 : Odd (k + 1) := by
    by_contra heven
    have hdvd2 : 2 ∣ (k + 1) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp heven)
    have hdvd2' : 2 ∣ (k + 3) := by
      obtain ⟨s, hs⟩ := hdvd2
      exact ⟨s + 1, by omega⟩
    have hhalf_dvd : (k + 3) / 2 ∣ (k + 3) := ⟨2, (Nat.div_mul_cancel hdvd2').symm⟩
    have hhalf_Z : (k + 3) / 2 ∣ 4 * Nat.factorial k + 2 :=
      dvd_trans hhalf_dvd g3
    have hhalf_fact : (k + 3) / 2 ∣ Nat.factorial k :=
      Nat.dvd_factorial (by omega) (by omega)
    have hhalf_4 : (k + 3) / 2 ∣ 4 * Nat.factorial k :=
      dvd_trans hhalf_fact (dvd_mul_left _ _)
    have hhalf_2 : (k + 3) / 2 ∣ 2 := by
      have hsub := Nat.dvd_sub hhalf_Z hhalf_4
      rwa [show 4 * Nat.factorial k + 2 - 4 * Nat.factorial k = 2 from by omega] at hsub
    have hle := Nat.le_of_dvd (by norm_num) hhalf_2
    omega
  have hprime1 : Nat.Prime (k + 1) := by
    by_contra hnot
    have h2le : 2 ≤ k + 1 := by omega
    have hmprime : Nat.Prime (k + 1).minFac := Nat.minFac_prime (by omega)
    have hmdvd : (k + 1).minFac ∣ (k + 1) := Nat.minFac_dvd _
    have hmle : (k + 1).minFac ≤ k := by
      have hle1 : (k + 1).minFac ≤ k + 1 := Nat.minFac_le_of_dvd h2le (dvd_refl _)
      have hne : (k + 1).minFac ≠ k + 1 := by
        intro heq
        apply hnot
        rw [Nat.prime_def_minFac]
        exact ⟨h2le, heq⟩
      omega
    have hmdvdF : (k + 1).minFac ∣ Nat.factorial k :=
      Nat.dvd_factorial (by have h2 := hmprime.two_le; omega) hmle
    have hmY : (k + 1).minFac ∣ 4 * (Nat.factorial k + 1) := dvd_trans hmdvd g1
    have hm4F : (k + 1).minFac ∣ 4 * Nat.factorial k :=
      dvd_trans hmdvdF (dvd_mul_left _ _)
    have hm4 : (k + 1).minFac ∣ 4 := by
      have hsub := Nat.dvd_sub hmY hm4F
      rwa [show 4 * (Nat.factorial k + 1) - 4 * Nat.factorial k = 4 from by omega] at hsub
    have h22 : (k + 1).minFac ∣ 2 * 2 := hm4
    rcases hmprime.dvd_mul.mp h22 with hh | hh
    · have m2 : (k + 1).minFac = 2 :=
        (Nat.prime_dvd_prime_iff_eq hmprime Nat.prime_two).mp hh
      have h2dvd : 2 ∣ (k + 1) := by rw [← m2]; exact hmdvd
      obtain ⟨a, ha⟩ := hodd1
      obtain ⟨b, hb⟩ := h2dvd
      omega
    · have m2 : (k + 1).minFac = 2 :=
        (Nat.prime_dvd_prime_iff_eq hmprime Nat.prime_two).mp hh
      have h2dvd : 2 ∣ (k + 1) := by rw [← m2]; exact hmdvd
      obtain ⟨a, ha⟩ := hodd1
      obtain ⟨b, hb⟩ := h2dvd
      omega
  have hodd3 : Odd (k + 3) := by
    obtain ⟨t, ht⟩ := hodd1
    exact ⟨t + 1, by omega⟩
  have hprime3 : Nat.Prime (k + 3) := by
    by_contra hnot
    have h2le : 2 ≤ k + 3 := by omega
    have hmprime : Nat.Prime (k + 3).minFac := Nat.minFac_prime (by omega)
    have hmdvd : (k + 3).minFac ∣ (k + 3) := Nat.minFac_dvd _
    have hmlt : (k + 3).minFac < k + 3 := by
      have hle1 : (k + 3).minFac ≤ k + 3 := Nat.minFac_le_of_dvd h2le (dvd_refl _)
      have hne : (k + 3).minFac ≠ k + 3 := by
        intro heq
        apply hnot
        rw [Nat.prime_def_minFac]
        exact ⟨h2le, heq⟩
      omega
    obtain ⟨t, ht⟩ := hmdvd
    have ht2 : 2 ≤ t := by
      by_contra hc
      have hc' : t < 2 := by omega
      interval_cases t <;> omega
    have hm2 : 2 * (k + 3).minFac ≤ k + 3 := by
      have hmul : (k + 3).minFac * 2 ≤ (k + 3).minFac * t :=
        Nat.mul_le_mul (le_refl _) ht2
      omega
    have hmle : (k + 3).minFac ≤ k := by omega
    have hmdvdF : (k + 3).minFac ∣ Nat.factorial k :=
      Nat.dvd_factorial (by have h2 := hmprime.two_le; omega) hmle
    have hmZ : (k + 3).minFac ∣ 4 * Nat.factorial k + 2 := dvd_trans ⟨t, ht⟩ g3
    have hm4F : (k + 3).minFac ∣ 4 * Nat.factorial k :=
      dvd_trans hmdvdF (dvd_mul_left _ _)
    have hm2dvd : (k + 3).minFac ∣ 2 := by
      have hsub := Nat.dvd_sub hmZ hm4F
      rwa [show 4 * Nat.factorial k + 2 - 4 * Nat.factorial k = 2 from by omega] at hsub
    have m2 : (k + 3).minFac = 2 :=
      (Nat.prime_dvd_prime_iff_eq hmprime Nat.prime_two).mp hm2dvd
    have h2dvd : 2 ∣ (k + 3) := by rw [← m2]; exact ⟨t, ht⟩
    obtain ⟨a, ha⟩ := hodd3
    obtain ⟨b, hb⟩ := h2dvd
    omega
  exact ⟨hprime1, hprime3⟩

/-- **Clement's criterion for twin primes.** For every natural number $p \ge 2$, the numbers
$p$ and $p + 2$ are both prime if and only if
$$4\bigl((p-1)! + 1\bigr) + p \equiv 0 \pmod{p(p+2)}.$$

The hypothesis $p \ge 2$ is needed: the unqualified restatement in the Journal of Integer
Sequences is false at $p = 1$.

Proves `Wanted` entry `clement_twin_prime_criterion`.

Source provenance (grounded ID `jis_grounded_f61a8741bce6c20e6c61e08b`):
* JIS restatement: `https://cs.uwaterloo.ca/journals/JIS/VOL13/Schmidt/multifact.tex`,
  lines 3295-3306, source SHA-256
  `0513d619381669719f263cd6f6d73963cb2ce17ba90a9ad280caff71060775f5`.
* Corrected domain: M. Chaves, `Twin Primes and a Primality Test by Indivisibility`,
  arXiv:math/0211034v3, source lines 110-121, citing P. A. Clement,
  `Congruences for Sets of Primes`, Amer. Math. Monthly 56 (1949), 23.
-/
theorem clement_twin_prime_criterion :
    ∀ (p : ℕ), 2 ≤ p →
      (Nat.Prime p ∧ Nat.Prime (p + 2) ↔
        Nat.ModEq (p * (p + 2)) (4 * (Nat.factorial (p - 1) + 1) + p) 0) := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2; decide
  by_cases h3 : p = 3
  · subst h3; decide
  by_cases h4 : p = 4
  · subst h4; decide
  · have hp5 : 5 ≤ p := by omega
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have hk : 4 ≤ k := by omega
    rw [Nat.add_sub_cancel, show k + 1 + 2 = k + 3 from by ring]
    rw [Nat.modEq_zero_iff_dvd]
    exact ⟨fun ⟨a, b⟩ => clement_aux_forward k hk a b,
      fun h => clement_aux_backward k hk h⟩

end MetaMathlibExt
