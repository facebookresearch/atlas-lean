/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Parity of the biunitary divisor sum

Only the odd biunitary divisors contribute to parity, and these are exactly the biunitary divisors
of the odd part. Unless that part is `1`, its biunitary divisors pair with their distinct
complements.
-/

namespace MetaMathlibExt

open Finset

private theorem mem_unitaryDivisors_mul_iff_of_coprime {d m a : ℕ} (hm : m ≠ 0) (ha : a ≠ 0)
    (hda : d.Coprime a) : d ∈ (m * a).unitaryDivisors ↔ d ∈ m.unitaryDivisors := by
  simp only [Nat.mem_unitaryDivisors, hda.dvd_mul_right]
  refine and_congr_right fun hd ↦ ?_
  have hdiv : (m * a) / d = (m / d) * a := by
    rw [Nat.mul_comm m a, Nat.mul_div_assoc _ hd, Nat.mul_comm a (m / d)]
  rw [hdiv, Nat.coprime_mul_iff_right]
  exact ⟨fun h ↦ ⟨hm, h.2.1⟩, fun h ↦ ⟨mul_ne_zero hm ha, h.2, hda⟩⟩

private theorem mem_biunitaryDivisors_mul_iff_of_coprime {d m a : ℕ} (hm : m ≠ 0) (ha : a ≠ 0)
    (hda : d.Coprime a) : d ∈ biunitaryDivisors (m * a) ↔ d ∈ biunitaryDivisors m := by
  simp only [mem_biunitaryDivisors, hda.dvd_mul_right]
  refine and_congr_right fun hd ↦ ?_
  have hdiv : (m * a) / d = (m / d) * a := by
    rw [Nat.mul_comm m a, Nat.mul_div_assoc _ hd, Nat.mul_comm a (m / d)]
  have hq : m / d ≠ 0 := by
    intro h
    exact hm (by simpa [h] using (Nat.div_mul_cancel hd).symm)
  have hinter : d.unitaryDivisors ∩ (m / d * a).unitaryDivisors =
      d.unitaryDivisors ∩ (m / d).unitaryDivisors := by
    ext e
    simp only [Finset.mem_inter]
    exact and_congr_right fun he ↦
      mem_unitaryDivisors_mul_iff_of_coprime hq ha
        (hda.of_dvd_left (Nat.dvd_of_mem_unitaryDivisors he))
  simp [hm, ha, hdiv, gcdUnitary, hinter]

private theorem odd_of_dvd_odd {d m : ℕ} (hd : d ∣ m) (hm : Odd m) : Odd d := by
  obtain ⟨a, rfl⟩ := hd
  exact Nat.Odd.of_mul_left hm

private theorem cast_sigmaBiunitary_mul_two_pow {m : ℕ} (hm : Odd m) (k : ℕ) :
    (sigmaBiunitary (m * 2 ^ k) : ZMod 2) = (sigmaBiunitary m : ZMod 2) := by
  have hm0 : m ≠ 0 := fun h ↦ Nat.not_odd_zero (h ▸ hm)
  have hmem (d : ℕ) (hodd : Odd d) :
      d ∈ biunitaryDivisors (m * 2 ^ k) ↔ d ∈ biunitaryDivisors m := by
    have hcop : d.Coprime 2 :=
      ((Nat.coprime_or_dvd_of_prime Nat.prime_two d).resolve_right hodd.not_two_dvd_nat).symm
    exact mem_biunitaryDivisors_mul_iff_of_coprime hm0 (by simp) (hcop.pow_right k)
  have hfilter : (biunitaryDivisors (m * 2 ^ k)).filter Odd = biunitaryDivisors m := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hodd⟩
      exact (hmem d hodd).mp hd
    · intro hd
      have hodd := odd_of_dvd_odd (dvd_of_mem_biunitaryDivisors hd) hm
      exact ⟨(hmem d hodd).mpr hd, hodd⟩
  simp only [sigmaBiunitary, Nat.cast_sum]
  rw [← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  split_ifs with h
  · rfl
  · exact ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp h)

private theorem even_sigmaBiunitary_of_odd {m : ℕ} (hm : Odd m) (hm1 : m ≠ 1) :
    Even (sigmaBiunitary m) := by
  rw [← ZMod.natCast_eq_zero_iff_even, sigmaBiunitary, Nat.cast_sum]
  have hm0 : m ≠ 0 := fun h ↦ Nat.not_odd_zero (h ▸ hm)
  have hdiv (d : ℕ) (hd : d ∈ biunitaryDivisors m) : m / (m / d) = d :=
    Nat.div_div_self (dvd_of_mem_biunitaryDivisors hd) hm0
  refine Finset.sum_involution (fun d _ ↦ m / d) ?_ ?_ ?_ hdiv
  · intro d hd
    have hdd := dvd_of_mem_biunitaryDivisors hd
    have hadd := (odd_of_dvd_odd hdd hm).add_odd (odd_of_dvd_odd (Nat.div_dvd_of_dvd hdd) hm)
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff_even]
    exact hadd
  · intro d hd _ hfix
    obtain ⟨hdd, -, hunit⟩ := mem_biunitaryDivisors.mp hd
    have hdpos := Nat.pos_of_dvd_of_pos hdd (Nat.pos_of_ne_zero hm0)
    have hself : d ∈ d.unitaryDivisors := by simp [hdpos.ne', Nat.div_self hdpos]
    rw [hfix] at hunit
    have hle := le_gcdUnitary hself hself
    rw [hunit] at hle
    have hd1 : d = 1 := le_antisymm hle hdpos
    exact hm1 (by simpa [hd1] using hfix)
  · intro d hd
    obtain ⟨hdd, hm0, hunit⟩ := mem_biunitaryDivisors.mp hd
    exact mem_biunitaryDivisors.mpr
      ⟨Nat.div_dvd_of_dvd hdd, hm0, by rwa [hdiv d hd, gcdUnitary_comm]⟩

/-- **Parity of the biunitary divisor sum.** For every positive integer $n$, the biunitary divisor
sum $\sigma^{**}(n)$ is odd if and only if $n = 2^k$ for some natural number $k$ (so $n = 1$ is
included).

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 2 (`jis-2025-25.4.5-lem-2`). -/
public theorem odd_sigmaBiunitary_iff (n : ℕ) (hn : 0 < n) :
    Odd (sigmaBiunitary n) ↔ ∃ k : ℕ, n = 2 ^ k := by
  have hm : Odd (ordCompl[2] n) :=
    Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp (Nat.not_dvd_ordCompl Nat.prime_two hn.ne'))
  have hfac : ordCompl[2] n * 2 ^ n.factorization 2 = n :=
    (Nat.mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self n 2)
  have hcast : (sigmaBiunitary n : ZMod 2) = (sigmaBiunitary (ordCompl[2] n) : ZMod 2) := by
    rw [← cast_sigmaBiunitary_mul_two_pow hm (n.factorization 2), hfac]
  have hpar : Odd (sigmaBiunitary n) ↔ Odd (sigmaBiunitary (ordCompl[2] n)) := by
    simp only [← Nat.not_even_iff_odd, ← ZMod.natCast_eq_zero_iff_even, hcast]
  rw [hpar]
  constructor
  · intro h
    have h1 : ordCompl[2] n = 1 := by
      by_contra hne
      exact (Nat.not_odd_iff_even.mpr (even_sigmaBiunitary_of_odd hm hne)) h
    exact ⟨n.factorization 2, by simpa only [h1, mul_one] using
      (Nat.ordProj_mul_ordCompl_eq_self n 2).symm⟩
  · rintro ⟨k, rfl⟩
    rw [Nat.ordCompl_self_pow Nat.prime_two, sigmaBiunitary_one]
    exact odd_one

end MetaMathlibExt
