/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import MathlibExt.Combinatorics.Enumerative.FubiniNumber
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Eventual periods of the Fubini numbers

The eventual periods modulo an odd integer are exactly the multiples of its Carmichael function.
We express the Fubini numbers modulo each odd prime power as weighted sums of powers and
isolate individual residue classes modulo the prime to detect the period.
-/

namespace MetaMathlibExt

open ArithmeticFunction Finset

namespace fubiniNumber_eventuallyPeriodic_iff_carmichael_dvd

/-- Summation by parts with geometric weights. -/
private lemma weighted_shift {R : Type*} [CommRing R] (b : R) (f : ℕ → R) (m : ℕ) :
    b * (∑ j ∈ range m, b ^ j * f (j + 1)) =
      (∑ j ∈ range m, b ^ j * f j) + b ^ m * f m - f 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, sum_range_succ, mul_add, ih, pow_succ]; ring

/-- Against weights with ratio one half, the falling factorial moments are factorials. -/
private lemma weighted_falling {R : Type*} [CommRing R] {b : R} (hb : 2 * b = 1)
    {m : ℕ} (hm : (m : R) = 0) (k : ℕ) :
    (∑ j ∈ range m, b ^ j * (j.descFactorial k : R)) =
      (∑ j ∈ range m, b ^ j) * k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    let f (j : ℕ) : R := j.descFactorial (k + 1)
    have hshift (j : ℕ) : f (j + 1) = f j + (k + 1 : ℕ) * (j.descFactorial k : R) := by
      have step : (j + 1).descFactorial (k + 1) =
          j.descFactorial (k + 1) + (k + 1) * j.descFactorial k := by
        rw [Nat.succ_descFactorial_succ]
        nlinarith [Nat.descFactorial_mul_self j k]
      simpa only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using
        congrArg (Nat.cast : ℕ → R) step
    have hboundary : f m = 0 := by
      cases m with
      | zero => simp [f]
      | succ m =>
        change ((m + 1).descFactorial (k + 1) : R) = 0
        rw [Nat.succ_descFactorial_succ, Nat.cast_mul, hm, zero_mul]
    have h := weighted_shift b f m
    simp only [hshift, hboundary, mul_zero, add_zero, show f 0 = 0 by simp [f], sub_zero,
      mul_add, sum_add_distrib] at h
    simp_rw [mul_left_comm (b ^ _) ((k + 1 : ℕ) : R)] at h
    rw [← mul_sum, ih] at h
    change (∑ j ∈ range m, b ^ j * f j) = _
    rw [Nat.factorial_succ, Nat.cast_mul]
    rw [← mul_add] at h
    have h₂ := congrArg (2 * ·) h
    rw [← mul_assoc, hb, one_mul] at h₂
    linear_combination -h₂

private lemma weighted_pow {R : Type*} [CommRing R] {b : R} (hb : 2 * b = 1)
    {m : ℕ} (hm : (m : R) = 0) (n : ℕ) :
    (∑ j ∈ range m, b ^ j * (j : R) ^ n) = (∑ j ∈ range m, b ^ j) * fubiniNumber n := by
  have expand (j : ℕ) : (j : R) ^ n = ∑ k ∈ range (n + 1),
      (Nat.stirlingSecond n k : R) * (j.descFactorial k : R) := by
    simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul] using
      congrArg (Nat.cast : ℕ → R) (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial j n)
  simp_rw [expand, mul_sum]
  rw [sum_comm, fubiniNumber_eq_sum, Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp_rw [mul_left_comm (b ^ _) (↑(Nat.stirlingSecond n k) : R), ← mul_sum,
    weighted_falling hb hm, Nat.cast_mul]
  ring

/-- A period annihilates each moment of the difference, also after multiplying by
any power of a translated variable. -/
private lemma translated_moment {m N p : ℕ}
    (h : ∀ n ≥ N, fubiniNumber (n + p) ≡ fubiniNumber n [MOD m])
    {b : ZMod m} (hb : 2 * b = 1) (c : ZMod m) (k n : ℕ) (hn : N ≤ n) :
    ∑ j ∈ range m, b ^ j * (j : ZMod m) ^ n * ((j : ZMod m) ^ p - 1) *
      ((j : ZMod m) + c) ^ k = 0 := by
  induction k generalizing n with
  | zero =>
    simp only [pow_zero, mul_one, mul_sub, mul_one, mul_assoc, ← pow_add, sum_sub_distrib]
    rw [weighted_pow hb (ZMod.natCast_self m), weighted_pow hb (ZMod.natCast_self m),
      (ZMod.natCast_eq_natCast_iff ..).mpr (h n hn), sub_self]
  | succ k ih =>
    have step (j : ℕ) : b ^ j * (j : ZMod m) ^ n * ((j : ZMod m) ^ p - 1) *
        ((j : ZMod m) + c) ^ (k + 1) =
        b ^ j * (j : ZMod m) ^ (n + 1) * ((j : ZMod m) ^ p - 1) * ((j : ZMod m) + c) ^ k +
        c * (b ^ j * (j : ZMod m) ^ n * ((j : ZMod m) ^ p - 1) * ((j : ZMod m) + c) ^ k) := by
      rw [pow_succ, pow_succ]; ring
    simp_rw [step, sum_add_distrib, ← mul_sum, ih n hn, ih (n + 1) (by omega), mul_zero, add_zero]

private lemma sum_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R) (q m : ℕ) :
    ∑ j ∈ range (m * q), f j = ∑ t ∈ range m, ∑ i ∈ range q, f (t * q + i) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

private lemma unit_pow_totient {d : ℕ} {x : ZMod d} (hx : IsUnit x) :
    x ^ d.totient = 1 := by
  obtain ⟨u, rfl⟩ := hx
  rw [← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one]

/-- Isolating the residue class of a unit modulo the underlying prime gives a
geometrically weighted power sum over all lifts of that residue. -/
private lemma class_moment {q r a N p : ℕ} (hq : q.Prime) (ha : 0 < a) (haq : a < q)
    (h : ∀ n ≥ N, fubiniNumber (n + p) ≡ fubiniNumber n [MOD q ^ (r + 1)])
    {b : ZMod (q ^ (r + 1))} (hb : 2 * b = 1) :
    ∑ t ∈ range (q ^ r), (b ^ q) ^ t * (((t * q + a : ℕ) : ZMod (q ^ (r + 1))) ^ p - 1) =
      0 := by
  let d := q ^ (r + 1)
  have : NeZero d := ⟨pow_ne_zero _ hq.ne_zero⟩
  let n := d.totient * (N + 1)
  let k := (r + 1) * d.totient
  have hn : N ≤ n := by
    have := Nat.totient_pos.mpr (NeZero.pos d)
    dsimp [n]; nlinarith
  -- The polynomial 1 - (X + q - a)^k selects precisely the lifts of a.
  let c : ZMod d := (q - a : ℕ)
  let w (j : ℕ) := b ^ j * (j : ZMod d) ^ n * ((j : ZMod d) ^ p - 1)
  have vanish : ∑ j ∈ range d, w j * (1 - ((j : ZMod d) + c) ^ k) = 0 := by
    simp only [mul_sub, mul_one, sum_sub_distrib]
    rw [show (∑ j ∈ range d, w j) = 0 by
      simpa [w] using translated_moment h hb c 0 n hn,
      show (∑ j ∈ range d, w j * ((j : ZMod d) + c) ^ k) = 0 from
        translated_moment h hb c k n hn, sub_zero]
  have block (t : ℕ) :
      (∑ i ∈ range q, w (t * q + i) * (1 - ((↑(t * q + i) : ZMod d) + c) ^ k)) =
      b ^ a * ((b ^ q) ^ t * (((t * q + a : ℕ) : ZMod d) ^ p - 1)) := by
    rw [sum_eq_single_of_mem a (mem_range.mpr haq)]
    · have hu : IsUnit (((t * q + a : ℕ) : ZMod d)) := by
        apply (ZMod.isUnit_natCast_iff_not_dvd_pow hq (Nat.succ_pos r)).mpr
        simpa [Nat.dvd_add_right (dvd_mul_left q t)] using Nat.not_dvd_of_pos_of_lt ha haq
      have hy : (↑(t * q + a) : ZMod d) + c = ((t + 1 : ℕ) : ZMod d) * q := by
        dsimp [c]; push_cast [Nat.cast_sub haq.le]; ring
      have hz : ((q : ZMod d) ^ (r + 1)) = 0 := by
        rw [← Nat.cast_pow]; exact ZMod.natCast_self d
      have hzero : ((↑(t * q + a) : ZMod d) + c) ^ k = 0 := by
        rw [hy, show k = (r + 1) * d.totient from rfl, pow_mul, mul_pow, hz, mul_zero,
          zero_pow (Nat.ne_of_gt (Nat.totient_pos.mpr (NeZero.pos d)))]
      simp only [w, n, pow_mul, unit_pow_totient hu, one_pow, mul_one, hzero, sub_zero]
      rw [pow_add b (t * q) a, ← pow_mul b q t, Nat.mul_comm q t]
      ring
    · intro i hi hia
      have hiq := mem_range.mp hi
      have hnd : ¬q ∣ i + (q - a) := by
        intro ⟨v, hv⟩
        rcases v with _ | _ | v
        · simp at hv; omega
        · simp at hv; omega
        · have := Nat.sub_le q a
          nlinarith
      have hu : IsUnit ((↑(t * q + i) : ZMod d) + c) := by
        change IsUnit ((↑(t * q + i) : ZMod d) + ↑(q - a))
        rw [← Nat.cast_add, Nat.add_assoc]
        exact (ZMod.isUnit_natCast_iff_not_dvd_pow hq (Nat.succ_pos r)).mpr
          ((Nat.dvd_add_right (dvd_mul_left q t)).not.mpr hnd)
      rw [show k = d.totient * (r + 1) by apply mul_comm, pow_mul, unit_pow_totient hu]
      simp
  change (∑ j ∈ range (q ^ r * q), _) = 0 at vanish
  rw [sum_blocks] at vanish
  simp_rw [block, ← mul_sum] at vanish
  have hunit := IsUnit.of_mul_eq_one 2 ((mul_comm b 2).trans hb)
  exact (hunit.pow a).mul_right_inj.mp (vanish.trans (mul_zero _).symm)

/-- The first nonconstant digit of a principal unit raised to a prime power. -/
private lemma principal_pow {q : ℕ} (ho : Odd q) (s : ℕ) (t : ℤ) :
    ∃ u : ℤ, (1 + q * t) ^ (q ^ s) = 1 + (q : ℤ) ^ (s + 1) * (t + q * u) := by
  induction s with
  | zero => exact ⟨0, by simp⟩
  | succ s ih =>
    obtain ⟨u, hu⟩ := ih
    let v := (q : ℤ) ^ s * (t + q * u)
    have hsum := odd_sq_dvd_geom_sum₂_sub (1 : ℤ) v ho
    simp only [one_pow, mul_one] at hsum
    obtain ⟨c, hc⟩ := hsum
    refine ⟨u + (t + q * u) * c, ?_⟩
    rw [pow_succ q s, pow_mul, hu, show (q : ℤ) ^ (s + 1) * (t + q * u) = q * v by
      dsimp [v]; rw [pow_succ]; ring, add_comm 1, ← geom_sum_mul_add]
    simp_rw [add_comm ((q : ℤ) * v) 1]
    rw [show (∑ i ∈ range q, (1 + (q : ℤ) * v) ^ i) = q + q ^ 2 * c by linarith]
    dsimp [v]
    ring

private lemma principal_pow_mul {q : ℕ} (ho : Odd q) (s k t : ℕ) :
    (((t * q + 1 : ℕ) : ZMod (q ^ (s + 2))) ^ (q ^ s * k) - 1) =
      (q : ZMod (q ^ (s + 2))) ^ (s + 1) * k * t := by
  obtain ⟨u, hu⟩ := principal_pow ho s (t : ℤ)
  let v := (q : ℤ) ^ (s + 1) * (t + q * u)
  obtain ⟨c, hc⟩ := sq_dvd_add_pow_sub_sub v (1 : ℤ) k
  simp only [one_pow, one_mul] at hc
  have h : (1 + (q : ℤ) * t) ^ (q ^ s * k) - 1 =
      (q : ℤ) ^ (s + 1) * k * t +
        (q : ℤ) ^ (s + 2) * (k * u + (q : ℤ) ^ s * (t + q * u) ^ 2 * c) := by
    rw [pow_mul, hu]
    dsimp [v] at hc
    linear_combination hc
  have heq := congrArg (Int.cast : ℤ → ZMod (q ^ (s + 2))) h
  push_cast at heq
  have hz : (q : ZMod (q ^ (s + 2))) ^ (s + 2) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hz, zero_mul, add_zero] at heq
  push_cast
  rw [mul_comm (t : ZMod (q ^ (s + 2))) (q : ZMod _), add_comm _ 1]
  exact heq

private lemma exists_half {d : ℕ} (ho : Odd d) :
    ∃ b : ℕ, (2 : ZMod d) * b = 1 := by
  obtain ⟨k, hk⟩ := ho
  refine ⟨k + 1, ?_⟩
  have eq : 2 * (k + 1) = d + 1 := by omega
  simpa using congrArg (Nat.cast : ℕ → ZMod d) eq

private lemma mass_mod_prime {q : ℕ} [Fact q.Prime] {b : ZMod q} (hb : 2 * b = 1) (s : ℕ) :
    ∑ t ∈ range (q ^ s), b ^ t = 1 := by
  have hne : b ≠ 1 := by
    rintro rfl
    exact one_ne_zero (by linear_combination hb)
  apply mul_right_cancel₀ (sub_ne_zero.mpr hne)
  rw [geom_sum_mul, ZMod.pow_card_pow, one_mul]

private lemma prime_sub_one_dvd_period {q N p : ℕ} (hq : q.Prime) (ho : Odd q)
    (h : ∀ n ≥ N, fubiniNumber (n + p) ≡ fubiniNumber n [MOD q]) :
    q - 1 ∣ p := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨b, hb⟩ := exists_half ho
  rw [← carmichael_of_prime hq, carmichael_eq_exponent hq.ne_zero,
    Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro u
  have ha : 0 < (u : ZMod q).val := Nat.pos_of_ne_zero fun hz =>
    u.ne_zero (by rw [← ZMod.natCast_zmod_val (u : ZMod q), hz, Nat.cast_zero])
  let d := q ^ (0 + 1)
  have hd : d = q := pow_one q
  have hb' : (2 : ZMod d) * b = 1 := hd ▸ hb
  have hh := class_moment (r := 0) hq ha (ZMod.val_lt _) (by simpa using h) hb'
  have hu : (((u : ZMod q).val : ZMod d) ^ p) = 1 := by
    simpa only [pow_zero, sum_range_one, zero_mul, zero_add, one_mul, sub_eq_zero] using hh
  rw [hd] at hu
  exact Units.ext (by simpa using hu)

private lemma reduce_period {d m N p : ℕ} (hd : d ∣ m)
    (h : ∀ n ≥ N, fubiniNumber (n + p) ≡ fubiniNumber n [MOD m]) :
    ∀ n ≥ N, fubiniNumber (n + p) ≡ fubiniNumber n [MOD d] :=
  fun n hn => (h n hn).of_dvd hd

/-- Each additional prime-power digit of the modulus forces a factor of the prime
in the period. Only the residue class of one is needed for this step. -/
private lemma prime_power_dvd_period {q N p : ℕ} (hq : q.Prime) (ho : Odd q) (s : ℕ)
    (h : ∀ n ≥ N, fubiniNumber (n + p) ≡ fubiniNumber n [MOD q ^ (s + 1)]) : q ^ s ∣ p := by
  induction s with
  | zero => simp
  | succ s ih =>
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨k, rfl⟩ := ih (reduce_period (pow_dvd_pow q (by omega)) h)
    let d := q ^ (s + 2)
    obtain ⟨b, hb⟩ := exists_half (show Odd d from ho.pow)
    have hc := class_moment (b := (b : ZMod d)) hq Nat.zero_lt_one hq.one_lt h hb
    -- On this class the first possible nonzero digit is k times its weighted first moment.
    let A := ∑ t ∈ range (q ^ (s + 1)), (b ^ q) ^ t * t
    have hdvd : d ∣ q ^ (s + 1) * (k * A) := by
      rw [← ZMod.natCast_eq_zero_iff]
      simp only [A, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, mul_sum]
      simp_rw [principal_pow_mul ho] at hc
      exact (sum_congr rfl fun t _ => by ring).trans hc
    have hdiv : q ∣ k * A := by
      change q ^ (s + 1 + 1) ∣ _ at hdvd
      rw [pow_succ, Nat.mul_dvd_mul_iff_left (pow_pos hq.pos _)] at hdvd
      exact hdvd
    have hqd : q ∣ d := dvd_pow_self q (by omega)
    have hbq : (2 : ZMod q) * b = 1 := by
      simpa only [map_mul, map_ofNat, map_natCast, map_one] using
        congrArg (ZMod.castHom hqd (ZMod q)) hb
    have hA : (A : ZMod q) = 1 := by
      simp only [A, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, ZMod.pow_card]
      have hf := weighted_falling hbq
        (show ((q ^ (s + 1) : ℕ) : ZMod q) = 0 from (ZMod.natCast_eq_zero_iff ..).mpr
          (dvd_pow_self q (by omega))) 1
      simpa only [Nat.descFactorial_one, Nat.factorial_one, Nat.cast_one, mul_one,
        mass_mod_prime hbq] using hf
    have hk : q ∣ k := (hq.dvd_mul.mp hdiv).resolve_right fun ha =>
      one_ne_zero (hA.symm.trans ((ZMod.natCast_eq_zero_iff ..).mpr ha))
    rw [pow_succ]
    exact Nat.mul_dvd_mul_left _ hk

private lemma prime_power_period {q s p : ℕ} (hq : q.Prime) (ho : Odd q)
    (hp : carmichael (q ^ (s + 1)) ∣ p) :
    ∀ n ≥ s + 1, fubiniNumber (n + p) ≡ fubiniNumber n [MOD q ^ (s + 1)] := by
  intro n hn
  let d := q ^ (s + 1)
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨b, hb⟩ := exists_half (show Odd d from ho.pow)
  have hbq : (2 : ZMod q) * b = 1 := by
    have hqd : q ∣ d := dvd_pow_self q (by omega)
    simpa only [map_mul, map_ofNat, map_natCast, map_one] using
      congrArg (ZMod.castHom hqd (ZMod q)) hb
  have hm : IsUnit (∑ j ∈ range d, (b : ZMod d) ^ j) := by
    simp only [← Nat.cast_pow, ← Nat.cast_sum]
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hq (Nat.succ_pos s)).mpr
    rw [← ZMod.natCast_eq_zero_iff]
    simpa only [Nat.cast_sum, Nat.cast_pow, d, mass_mod_prime hbq] using
      (one_ne_zero : (1 : ZMod q) ≠ 0)
  rw [← ZMod.natCast_eq_natCast_iff]
  apply hm.mul_right_inj.mp
  rw [← weighted_pow hb (ZMod.natCast_self d), ← weighted_pow hb (ZMod.natCast_self d)]
  refine sum_congr rfl fun j _ => congrArg _ ?_
  rw [pow_add]
  by_cases hj : q ∣ j
  · have hz : (j : ZMod d) ^ n = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact (pow_dvd_pow q hn).trans (pow_dvd_pow_of_dvd hj n)
    rw [hz, zero_mul]
  · obtain ⟨u, hu⟩ := (ZMod.isUnit_natCast_iff_not_dvd_pow hq (Nat.succ_pos s)).mpr hj
    obtain ⟨k, hk⟩ := hp
    have hu₁ := congrArg (fun z : (ZMod d)ˣ => (z : ZMod d)) (pow_carmichael u)
    rw [hk, pow_mul, ← hu]
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hu₁
    rw [hu₁, one_pow, mul_one]

end fubiniNumber_eventuallyPeriodic_iff_carmichael_dvd

open fubiniNumber_eventuallyPeriodic_iff_carmichael_dvd

/-- **Eventual periods of the Fubini numbers modulo an odd number.** Let $K$ be an odd natural
number and let $\lambda(K)$ be the value of the Carmichael function at $K$. Then a natural number
$p$ is divisible by $\lambda(K)$ if and only if there is a natural number $N$ such that the Fubini
numbers $F(n)$ satisfy $F(n + p) \equiv F(n) \pmod K$ for all $n \ge N$. In particular, the
eventual period of the Fubini numbers modulo $K$ is exactly $\lambda(K)$.

Source: Benjamin Schreyer, *Rigged Horse Numbers and their Modular Periodicity*, Journal of
Integer Sequences 28 (2025), Article 25.4.1, Corollary 11 (`jis-2025-25.4.1-cor-11`). -/
public theorem fubiniNumber_eventuallyPeriodic_iff_carmichael_dvd (K : ℕ) (hK : Odd K)
    (p : ℕ) :
    (∃ N, ∀ n ≥ N, fubiniNumber (n + p) ≡ fubiniNumber n [MOD K]) ↔ carmichael K ∣ p := by
  induction K using Nat.recOnPosPrimePosCoprime with
  | zero => simp at hK
  | one => simp [Nat.modEq_one]
  | prime_pow q r hq hr =>
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    have ho := (Nat.odd_pow_iff (Nat.succ_ne_zero s)).mp hK
    refine ⟨?_, fun hp => ⟨s + 1, prime_power_period hq ho hp⟩⟩
    rintro ⟨N, h⟩
    rw [carmichael_pow_of_prime_ne_two _ hq (by rintro rfl; exact (by decide : ¬ Odd 2) ho),
      Nat.totient_prime_pow_succ hq]
    have hc : q.Coprime (q - 1) :=
      (Nat.coprime_self_sub_right hq.pos).mpr (Nat.coprime_one_right q)
    exact (hc.pow_left s).mul_dvd_of_dvd_of_dvd (prime_power_dvd_period hq ho s h)
      (prime_sub_one_dvd_period hq ho (reduce_period (dvd_pow_self q (by omega)) h))
  | coprime a b _ _ hab iha ihb =>
    rw [carmichael_mul hab, Nat.lcm_dvd_iff]
    rw [← iha (hK.of_dvd_nat (dvd_mul_right a b)), ← ihb (hK.of_dvd_nat (dvd_mul_left b a))]
    constructor
    · rintro ⟨N, h⟩
      exact ⟨⟨N, reduce_period (dvd_mul_right a b) h⟩, ⟨N, reduce_period (dvd_mul_left b a) h⟩⟩
    · rintro ⟨⟨A, ha⟩, ⟨B, hb⟩⟩
      exact ⟨max A B, fun n hn => (Nat.modEq_and_modEq_iff_modEq_mul hab).mp
        ⟨ha n ((le_max_left ..).trans hn), hb n ((le_max_right ..).trans hn)⟩⟩

end MetaMathlibExt
