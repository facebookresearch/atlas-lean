/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import MathlibExt.NumberTheory.StrongPseudoprime
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Strong pseudoprimes from cyclotomic values

Composite divisors of the primitive parts of `b ^ m - 1` and `b ^ m + 1` are strong
pseudoprimes to base `b` after removing the intrinsic prime factor.
-/

namespace MetaMathlibExt

open Polynomial

namespace isStrongPseudoprime_of_dvd_primitivePart

private theorem eval_dvd_geom_sum {b : ℤ} (hb : 1 < b) {d t : ℕ} (hd : 0 < d)
    (ht : 1 < t) :
    (cyclotomic (d * t) ℤ).eval b ∣ ∑ i ∈ Finset.range t, (b ^ d) ^ i := by
  have hproper : d ∈ (d * t).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨dvd_mul_right .., lt_mul_of_one_lt_right hd ht⟩
  have hdiv : (b ^ d - 1) * (cyclotomic (d * t) ℤ).eval b ∣ (b ^ d) ^ t - 1 := by
    simpa [pow_mul] using eval_dvd (x := b)
      (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hproper)
  rwa [← mul_geom_sum (b ^ d) t,
    mul_dvd_mul_iff_left (sub_ne_zero.mpr (one_lt_pow₀ hb hd.ne').ne')] at hdiv

-- If `p` divides the index, the geometric sum bounds its multiplicity in the cyclotomic value.
private theorem sq_not_dvd_eval {b d p : ℕ} (hb : 1 < b) (hd : 0 < d) (hp : p.Prime)
    (hpow : (b : ZMod p) ^ d = 1) (heven : p = 2 → Even d) :
    ¬ (p : ℤ) ^ 2 ∣ (cyclotomic (d * p) ℤ).eval (b : ℤ) := by
  have hdiv := eval_dvd_geom_sum (b := (b : ℤ)) (by exact_mod_cast hb) hd hp.one_lt
  intro hsq
  have hs := hsq.trans hdiv
  let x : ℤ := (b : ℤ) ^ d
  have hx : (x : ZMod p) = 1 := by simpa [x] using hpow
  by_cases hp2 : p = 2
  · have hd2 := heven hp2
    subst p
    have hbodd : Odd (b : ℤ) := by
      have hb0 : (b : ZMod 2) ≠ 0 := fun h => by simp [h, hd.ne'] at hpow
      have : Odd b := Nat.not_even_iff_odd.mp (fun h => hb0 h.natCast_zmod_two)
      exact_mod_cast this
    obtain ⟨e, he⟩ := hd2
    have hx4 : x % 4 = 1 := by
      change (b : ℤ) ^ d % 4 = 1
      rw [show d = e * 2 by omega, pow_mul]
      exact Int.sq_emod_four_eq_one_of_odd (hbodd.pow)
    have hfour : (4 : ℤ) ∣ 1 + x := by
      simpa [x, Finset.sum_range_succ] using hs
    rw [Int.dvd_iff_emod_eq_zero, Int.add_emod, hx4] at hfour
    norm_num at hfour
  · have hsub : (p : ℤ) ∣ x - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp [hx]
    have hunit : ¬ (p : ℤ) ∣ x := by
      have : Fact p.Prime := ⟨hp⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hx]
      exact one_ne_zero
    have hmult : emultiplicity (p : ℤ) (∑ i ∈ Finset.range p, x ^ i) = 1 := by
      simpa using emultiplicity_geom_sum₂_eq_one (Nat.prime_iff_prime_int.mp hp)
        (hp.odd_of_ne_two hp2) hsub hunit
    exact ((emultiplicity_eq_coe (n := 1)).mp hmult).2 hs

-- A prime surviving the gcd removal must be prime to the index.
private theorem index_dvd_prime_sub_one {b n m p : ℕ} (hb : 1 < b) (hn : 2 < n)
    (hnm : n = m ∨ n = 2 * m) (hp : p.Prime)
    (h : (p : ℤ) ∣ (cyclotomic n ℤ).eval (b : ℤ) /
      (Int.gcd ((cyclotomic n ℤ).eval (b : ℤ)) m : ℤ)) : n ∣ p - 1 := by
  let v := (cyclotomic n ℤ).eval (b : ℤ)
  have hg := Int.gcd_dvd_left v (m : ℤ)
  have hpv : (p : ℤ) ∣ v := dvd_trans h (Int.ediv_dvd_of_dvd hg)
  have : Fact p.Prime := ⟨hp⟩
  have hroot : (cyclotomic n (ZMod p)).IsRoot (b : ZMod p) := by
    simpa [IsRoot.def, v] using
      (cyclotomic.eval_apply (b : ℤ) n (Int.castRingHom (ZMod p))).trans
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpv)
  -- In characteristic `p`, the root's order is the prime-to-`p` part of the index.
  obtain ⟨k, r, hpr, hnr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
  have hr : 0 < r := Nat.pos_of_ne_zero (fun hzero => hpr (hzero ▸ dvd_zero p))
  have : NeZero (r : ZMod p) := NeZero.of_not_dvd (ZMod p) hpr
  have hprim : IsPrimitiveRoot (b : ZMod p) r :=
    isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp (hnr ▸ hroot)
  have horder := ZMod.orderOf_dvd_card_sub_one (hprim.ne_zero hr.ne')
  rw [← hprim.eq_orderOf] at horder
  cases k with
  | zero => simpa [hnr] using horder
  | succ k =>
    have hnd : n = (r * p ^ k) * p := by rw [hnr, pow_succ]; ac_rfl
    have hpn : p ∣ n := hnd ▸ dvd_mul_left ..
    have htwo (hp2 : p = 2) : r = 1 ∧ 0 < k := by
      have hdiv : r ∣ 1 := by simpa [hp2] using horder
      have hr1 := Nat.dvd_one.mp hdiv
      refine ⟨hr1, Nat.pos_of_ne_zero ?_⟩
      intro hk
      simp [hr1, hp2, hk] at hnd
      omega
    have hpm : p ∣ m := by
      rcases hnm with rfl | hnm
      · exact hpn
      rw [hnm] at hpn
      by_cases hp2 : p = 2
      · obtain ⟨hr1, hk⟩ := htwo hp2
        have hnd' : 2 * m = 2 ^ k * 2 := by simpa [hnm, hr1, hp2] using hnd
        have hm' : m = 2 ^ k := by omega
        rw [hp2, hm']
        exact dvd_pow_self 2 hk.ne'
      · exact (hp.dvd_mul.mp hpn).resolve_left (by
          rwa [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two])
    have hpg : (p : ℤ) ∣ (Int.gcd v (m : ℤ) : ℤ) :=
      Int.dvd_coe_gcd hpv (Int.natCast_dvd_natCast.mpr hpm)
    have hsq : (p : ℤ) ^ 2 ∣ v := by
      rw [pow_two]
      exact (mul_dvd_mul hpg h).trans (Int.dvd_div_iff_mul_dvd hg |>.mp dvd_rfl)
    have hpow : (b : ZMod p) ^ (r * p ^ k) = 1 := by
      rw [pow_mul, hprim.pow_eq_one, one_pow]
    have heven (hp2 : p = 2) : Even (r * p ^ k) := by
      rw [hp2, even_iff_two_dvd]
      exact dvd_mul_of_dvd_right (dvd_pow_self 2 (htwo hp2).2.ne') _
    change (p : ℤ) ^ 2 ∣ (cyclotomic n ℤ).eval (b : ℤ) at hsq
    rw [hnd] at hsq
    exact (sq_not_dvd_eval hb (Nat.mul_pos hr (pow_pos hp.pos _)) hp hpow heven hsq).elim

private theorem modEq_one_of_prime_divisors {n c : ℕ} (hc : c ≠ 0)
    (h : ∀ p, p.Prime → p ∣ c → n ∣ p - 1) : 1 ≡ c [MOD n] := by
  induction c using Nat.recOnMul with
  | zero => exact (hc rfl).elim
  | one => rfl
  | prime p hp => exact (Nat.modEq_iff_dvd' hp.one_lt.le).mpr (h p hp dvd_rfl)
  | mul a b ha hb =>
    have ha' := ha (left_ne_zero_of_mul hc) (fun p hp hd => h p hp (hd.trans (dvd_mul_right ..)))
    have hb' := hb (right_ne_zero_of_mul hc) (fun p hp hd => h p hp (hd.trans (dvd_mul_left ..)))
    simpa only [one_mul] using ha'.mul hb'

private theorem of_dvd_quotient {b n m c : ℕ} (hb : 1 < b) (hn : 2 < n)
    (hnm : n = m ∨ n = 2 * m) (hc : 1 < c) (hcomp : ¬c.Prime)
    (h : (c : ℤ) ∣ (cyclotomic n ℤ).eval (b : ℤ) /
      (Int.gcd ((cyclotomic n ℤ).eval (b : ℤ)) m : ℤ)) : IsStrongPseudoprime c b := by
  have hp (p : ℕ) (hp : p.Prime) (hpc : p ∣ c) : n ∣ p - 1 :=
    index_dvd_prime_sub_one hb hn hnm hp ((Int.natCast_dvd_natCast.mpr hpc).trans h)
  have hodd : Odd c := Nat.not_even_iff_odd.mp fun he => by
    have := Nat.dvd_one.mp (hp 2 Nat.prime_two he.two_dvd)
    omega
  have hc0 : c ≠ 0 := by omega
  -- Split both factors of `c - 1 = n * q` into their powers of two and odd parts.
  obtain ⟨q, hq⟩ := (modEq_one_of_prime_divisors hc0 hp).dvd'
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq; omega
  obtain ⟨j, t, ht, hqt⟩ := Nat.exists_eq_two_pow_mul_odd hq0
  obtain ⟨a, s, hs, hns⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have hcv : (c : ℤ) ∣ (cyclotomic n ℤ).eval (b : ℤ) :=
    h.trans (Int.ediv_dvd_of_dvd (Int.gcd_dvd_left ..))
  refine ⟨hc, hcomp, hodd, a + j, s * t, ?_, hs.mul ht, ?_⟩
  · rw [hq, hqt, hns, pow_add]; ac_rfl
  cases a with
  | zero =>
    have heq : n = s := by simpa using hns
    have hdiv : (c : ℤ) ∣ (b : ℤ) ^ s - 1 := hcv.trans (by
      simpa [heq] using eval_dvd (x := (b : ℤ)) (cyclotomic.dvd_X_pow_sub_one n ℤ))
    have hpow : (b : ZMod c) ^ s = 1 := by
      rw [← sub_eq_zero]
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
    exact Or.inl (by rw [pow_mul, hpow, one_pow])
  | succ a =>
    have heq : n = (2 ^ a * s) * 2 := by rw [hns, pow_succ]; ac_rfl
    have hdiv : (c : ℤ) ∣ (b : ℤ) ^ (2 ^ a * s) + 1 := hcv.trans (by
      simpa [heq, Finset.sum_range_succ, add_comm] using
        eval_dvd_geom_sum (b := (b : ℤ)) (by exact_mod_cast hb)
          (d := 2 ^ a * s) (Nat.mul_pos (by positivity) hs.pos) (t := 2) (by decide))
    have hpow : (b : ZMod c) ^ (2 ^ a * s) = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
    exact Or.inr ⟨a, by omega, by rw [← mul_assoc, pow_mul, hpow, ht.neg_one_pow]⟩

end isStrongPseudoprime_of_dvd_primitivePart

/-- **Composite divisors of primitive parts without their intrinsic factor are strong
pseudoprimes.** Let $b > 1$ and $m > 2$ be natural numbers, and let $\Phi_j$ denote the $j$-th
cyclotomic polynomial. If a composite natural number $c > 1$ divides
$\Phi_m(b) / \gcd(\Phi_m(b), m)$ or $\Phi_{2m}(b) / \gcd(\Phi_{2m}(b), m)$, then $c$ is a strong
pseudoprime to the base $b$.

Here $\Phi_m(b)$ and $\Phi_{2m}(b)$ are the primitive parts of $b^m - 1$ and $b^m + 1$, and
dividing by the greatest common divisor with $m$ removes the intrinsic prime factor, if any.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 5 (`integers-2024-A23-thm-5`). -/
public theorem isStrongPseudoprime_of_dvd_primitivePart {b m c : ℕ} (hb : 1 < b)
    (hm : 2 < m) (hc : 1 < c) (hcomp : ¬c.Prime) :
    let Φ : ℕ → ℤ := fun j => (Polynomial.cyclotomic j ℤ).eval (b : ℤ)
    ((c : ℤ) ∣ Φ m / (Int.gcd (Φ m) m : ℤ) ∨
      (c : ℤ) ∣ Φ (2 * m) / (Int.gcd (Φ (2 * m)) m : ℤ)) →
      IsStrongPseudoprime c b := by
  dsimp only
  rintro (h | h)
  · exact isStrongPseudoprime_of_dvd_primitivePart.of_dvd_quotient hb hm (Or.inl rfl) hc hcomp h
  · exact isStrongPseudoprime_of_dvd_primitivePart.of_dvd_quotient hb (by omega) (Or.inr rfl)
      hc hcomp h

end MetaMathlibExt
