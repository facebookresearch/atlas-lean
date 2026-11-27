/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Restricted Erdős–Straus representations of primes

Chamberland's characterization relates the representations of `4/p` with exactly two denominators
divisible by `p` to pairs of divisors of `(q + 1)/4` for `q ≡ 3` modulo four.
-/

namespace MathlibExt.NumberTheory.ErdosStrausPrimeStructureWanted

private theorem clear_denominators {p a u v : ℕ}
    (hp : 0 < p) (ha : 0 < a) (hu : 0 < u) (hv : 0 < v) :
    ((4 : ℚ) / p = 1 / a + 1 / (p * u : ℕ) + 1 / (p * v : ℕ)) ↔
      4 * a * u * v = p * u * v + a * v + a * u := by
  push_cast
  field_simp [hp.ne', ha.ne', hu.ne', hv.ne']
  rw [add_mul]
  norm_cast

/-- **Chamberland's characterization of restricted Erdős–Straus representations.** For a prime
$p$, there are positive integers $a \le b \le c$ with $p \nmid a$, $p \mid b$, $p \mid c$ and
$4/p = 1/a + 1/b + 1/c$ if and only if there are positive integers $q$, $r$, $s_1$, $s_2$ with
$q \equiv 3 \pmod 4$, both $s_1$ and $s_2$ dividing $(q + 1)/4$, and $p + 4 s_1 s_2 = qr$.

Source: Marc Chamberland, "The Erdős-Straus Conjecture and the
Structure of Primes", Theorem 1. -/
public theorem erdos_straus_prime_restricted_representation_iff
    (p : ℕ) (hp : p.Prime) :
    (∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≤ b ∧ b ≤ c ∧
      ¬p ∣ a ∧ p ∣ b ∧ p ∣ c ∧
      (4 : ℚ) / p = 1 / a + 1 / b + 1 / c) ↔
    (∃ q r s₁ s₂ : ℕ, 0 < q ∧ 0 < r ∧ 0 < s₁ ∧ 0 < s₂ ∧
      q % 4 = 3 ∧ s₁ ∣ (q + 1) / 4 ∧ s₂ ∣ (q + 1) / 4 ∧
      p + 4 * s₁ * s₂ = q * r) := by
  constructor
  · rintro ⟨a, _, _, ha, hb, hc, _, _, hpa, ⟨u, rfl⟩, ⟨v, rfl⟩, h⟩
    have hu := Nat.pos_of_mul_pos_left hb
    have hv := Nat.pos_of_mul_pos_left hc
    have heq := (clear_denominators hp.pos ha hu hv).mp h
    -- With q = 4u - 1, the excess d = qa - pu satisfies dv = au.
    let q := 4 * u - 1
    have hq : q + 1 = 4 * u := by dsimp [q]; omega
    have hqa : q * a * v = p * u * v + a * u := by
      linear_combination heq + a * v * hq
    have hlt : p * u < q * a := by
      apply Nat.lt_of_mul_lt_mul_right (a := v)
      rw [hqa]
      exact Nat.lt_add_of_pos_right (Nat.mul_pos ha hu)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlt.le
    have hdv : d * v = a * u := by rw [hd, Nat.add_mul] at hqa; omega
    -- The identity qau = pu² + du gives d ∣ pu². Primality removes the factor p.
    have hdiv : d ∣ p * (u * u) := by
      apply (Nat.dvd_add_left (dvd_mul_right d u)).mp
      calc
        d ∣ q * (d * v) := dvd_mul_of_dvd_right (dvd_mul_right d v) q
        _ = p * (u * u) + d * u := by rw [hdv]; linear_combination u * hd
    have hpd : ¬ p ∣ d := by
      intro hpd
      have hpu := (hp.dvd_mul.mp (hdv ▸ dvd_mul_of_dvd_left hpd v)).resolve_left hpa
      have hpqa : p ∣ q * a := hd ▸ Nat.dvd_add (dvd_mul_right p u) hpd
      have hpq := (hp.dvd_mul.mp hpqa).resolve_right hpa
      exact hp.not_dvd_one ((Nat.dvd_add_right hpq).mp (hq ▸ dvd_mul_of_dvd_right hpu 4))
    obtain ⟨s₁, s₂, hs₁, hs₂, hds⟩ := Nat.dvd_mul.mp
      ((hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_of_dvd_mul_left hdiv)
    have hrlt : p < 4 * a := by
      apply Nat.lt_of_mul_lt_mul_right (a := u * v)
      nlinarith only [heq, Nat.mul_pos ha hu]
    let r := 4 * a - p
    have hr : r + p = 4 * a := by dsimp [r]; omega
    have huq : (q + 1) / 4 = u := by omega
    refine ⟨q, r, s₁, s₂, by omega, by omega, Nat.pos_of_dvd_of_pos hs₁ hu,
      Nat.pos_of_dvd_of_pos hs₂ hu, by omega, huq ▸ hs₁, huq ▸ hs₂, ?_⟩
    rw [mul_assoc 4, hds]
    linear_combination 4 * hd.symm + p * hq + q * hr.symm
  · rintro ⟨q, r, s₁, s₂, _, hr, _, _, hmod, h₁, h₂, hqr⟩
    let u := (q + 1) / 4
    let d := s₁ * s₂
    have hq : q + 1 = 4 * u := by dsimp [u]; omega
    have hu : 0 < u := by omega
    have hprod : p + r + 4 * d = 4 * (u * r) := by
      dsimp [d]
      linear_combination hqr + r * hq
    -- Recover a from 4a = p + r. Since d divides u², it also divides au.
    let a := u * r - d
    have haeq : a + d = u * r := by dsimp [a]; omega
    have ha4 : 4 * a = p + r := by omega
    have ha : 0 < a := by omega
    have hadiv : d ∣ a * u := by
      apply (Nat.dvd_add_left (dvd_mul_right d u)).mp
      calc
        d ∣ (u * u) * r := dvd_mul_of_dvd_left (Nat.mul_dvd_mul h₁ h₂) r
        _ = a * u + d * u := by linear_combination u * haeq.symm
    obtain ⟨v, hdv⟩ := hadiv
    have hv : 0 < v := Nat.pos_of_mul_pos_left (hdv ▸ Nat.mul_pos ha hu)
    have heq : 4 * a * u * v = p * u * v + a * v + a * u := by
      linear_combination u * v * ha4 + v * haeq.symm + hdv.symm
    -- Positivity of u and v gives 1/u + 1/v ≤ 2, hence 2a ≤ p.
    have hap : a < p := by
      have hbound : 2 * a * (u * v) ≤ p * (u * v) := by
        nlinarith only [heq, Nat.le_mul_of_pos_right (a * u) hv,
          Nat.le_mul_of_pos_right (a * v) hu]
      have := Nat.le_of_mul_le_mul_right hbound (Nat.mul_pos hu hv)
      omega
    have h := (clear_denominators hp.pos ha hu hv).mpr heq
    have hau := hap.le.trans (Nat.le_mul_of_pos_right p hu)
    have hav := hap.le.trans (Nat.le_mul_of_pos_right p hv)
    have hpa := Nat.not_dvd_of_pos_of_lt ha hap
    have hb := Nat.mul_pos hp.pos hu
    have hc := Nat.mul_pos hp.pos hv
    rcases le_total (p * u) (p * v) with huv | hvu
    · exact ⟨a, p * u, p * v, ha, hb, hc, hau, huv, hpa,
        dvd_mul_right p u, dvd_mul_right p v, h⟩
    · exact ⟨a, p * v, p * u, ha, hc, hb, hav, hvu, hpa,
        dvd_mul_right p v, dvd_mul_right p u, by rwa [add_right_comm]⟩

end MathlibExt.NumberTheory.ErdosStrausPrimeStructureWanted
