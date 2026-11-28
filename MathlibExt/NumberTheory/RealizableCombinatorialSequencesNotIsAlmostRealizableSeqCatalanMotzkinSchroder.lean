/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.Schroder
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
public import MathlibExt.Combinatorics.Enumerative.ZagierNumber
public import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
public import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusGeometricGrowth
public import MathlibExt.NumberTheory.DoldPrimePowerCongruences
public import MathlibExt.NumberTheory.HelouTerjanianLargePrime
public import MathlibExt.NumberTheory.HelouTerjanianTwo
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.RingTheory.PowerSeries.Schroder
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ComputeDegree
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Catalan, Motzkin and large Schröder numbers are not almost realizable

Defines almost realizability and proves that these three sequences are not almost realizable.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Theorem 21 (`jis-2024-24.3.3-thm-21`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Almost realizable sequences.** A sequence $a$ of natural numbers $a(0), a(1), \dots$ is
almost realizable when there is an integer $m \ge 1$ such that the integer sequence
$(m\, a(n))_{n \ge 0}$ is Dold realizable: for every $n \ge 1$, the sum
$\sum_{d \mid n} \mu(d)\, m\, a(n/d)$ over the positive divisors $d$ of $n$, where $\mu$ is the
Möbius function, is non-negative and divisible by $n$.

This is Miska and Ward's notion that some positive integer multiple of $a$ is realizable. The
value $a(0)$ is not used.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Definition 3. -/
def IsAlmostRealizableSeq (a : ℕ → ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ doldRealizable fun n => ((m * a n : ℕ) : ℤ)

open Finset
private theorem catalan_prime_zmod (p : ℕ) (hp : p.Prime) :
    (catalan p : ZMod p) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have h := congrArg (fun n : ℕ => (n : ZMod p)) (succ_mul_catalan_eq_centralBinom p)
  have hc := Choose.choose_mul_mul_modEq_choose_nat (p := p) (a := 2) (b := 1)
  have hc' : ((2 * p).choose p : ZMod p) = 2 := by
    simpa [mul_comm] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc
  simpa [Nat.centralBinom_eq_two_mul_choose, hc'] using h
private theorem motzkin_two_prime_zmod (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (motzkinNumber (2 * p) : ZMod p) = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [motzkinNumber_eq_sum_range_half]
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), sum_range_succ]
  push_cast
  simp only [Nat.choose_self, Nat.cast_one, one_mul, catalan_prime_zmod p hp]
  have hs : ∑ k ∈ range p, ((2 * p).choose (2 * k) : ZMod p) * (catalan k : ZMod p) = 1 := by
    rw [sum_eq_single 0]
    · simp
    · intro k hk hk0
      have hk' := mem_range.mp hk
      have hpk : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk'
      have hp2' : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) hp2
      have hnd : ¬ p ∣ 2 * k := fun h => (hp.dvd_mul.mp h).elim hp2' hpk
      have hmod : 2 * k % p ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
      have hc := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := 2 * p) (k := 2 * k) (p := p)
      have hz : ((2 * p).choose (2 * k) : ZMod p) = 0 := by
        have hnmod : 2 * p % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_left p 2)
        simpa only [hnmod, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hmod),
          zero_mul, Nat.cast_zero] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc
      rw [hz, zero_mul]
    · intro h
      exact False.elim (h (mem_range.mpr hp.pos))
  rw [hs]
  norm_num
private theorem dold_prime_zmod (a : ℕ → ℕ) (m p n : ℕ) (hp : p.Prime)
    (hn : 0 < n) (h : doldRealizable fun k => ((m * a k : ℕ) : ℤ)) :
    (m : ZMod p) * (a (n * p) : ZMod p) = (m : ZMod p) * (a n : ZMod p) := by
  have hd : ∀ k : ℕ, 1 ≤ k → (k : ℤ) ∣ ∑ d ∈ k.divisors,
      (ArithmeticFunction.moebius (k / d) : ℤ) * ((m * a d : ℕ) : ℤ) := by
    intro k hk
    have he : (∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k / d) : ℤ) *
        ((m * a d : ℕ) : ℤ)) = ∑ d ∈ k.divisors,
        (ArithmeticFunction.moebius d : ℤ) * ((m * a (k / d) : ℕ) : ℤ) := by
      rw [← Nat.sum_div_divisors k]
      apply sum_congr rfl
      intro d hd
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (by omega : k ≠ 0)]
    rw [he]
    exact (h k hk).1
  have hc := (prime_power_congruence_iff_dold _).mpr hd n 1 p hn (by omega) hp
  have hc' : ((m * a (n * p) : ℕ) : ZMod p) = ((m * a n : ℕ) : ZMod p) := by
    have hh := (ZMod.intCast_eq_intCast_iff _ _ p).mpr (by simpa using hc)
    simpa using hh
  simpa only [Nat.cast_mul] using hc'
private theorem coeff_prime_pow (p : ℕ) (hp : p.Prime)
    (f : PowerSeries (ZMod p)) (n : ℕ) :
    PowerSeries.coeff n (f ^ p) =
      if p ∣ n then PowerSeries.coeff (n / p) f else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have he : f.expand p hp.ne_zero = f ^ p := by
    simpa only [ZMod.card] using FiniteField.PowerSeries.expand_card f
  rw [← he, PowerSeries.coeff_expand]
open PowerSeries in
private theorem schroder_prime_zmod (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (Nat.largeSchroder p : ZMod p) = 4 := by
  have : Fact p.Prime := ⟨hp⟩
  let S := PowerSeries.map (Nat.castRingHom (ZMod p)) PowerSeries.largeSchroderSeries
  have hs (n : ℕ) : PowerSeries.coeff n S = (Nat.largeSchroder n : ZMod p) := by
    simp [S]
  have he : S = 1 + PowerSeries.X * S + PowerSeries.X * S ^ 2 := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom (ZMod p)))
      largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
    simpa [S] using h
  let F : PowerSeries (ZMod p) := PowerSeries.X * S
  let H : PowerSeries (ZMod p) := 1 - PowerSeries.X - 2 * F
  let D : PowerSeries (ZMod p) := PowerSeries.X ^ 2 - 6 * PowerSeries.X + 1
  have hsq : H ^ 2 = D := by
    dsimp [H, D, F]
    linear_combination -4 * PowerSeries.X * he
  obtain ⟨r, hr⟩ := hp.odd_of_ne_two (by omega)
  have hpr : p = 2 * r + 1 := by omega
  have hpower : H * D ^ p = H ^ p * D ^ (r + 1) := by
    rw [← hsq, ← pow_mul, ← pow_mul, ← pow_add, ← pow_succ']
    congr 1
    omega
  have hex (f : PowerSeries (ZMod p)) : f.expand p hp.ne_zero = f ^ p := by
    simpa only [ZMod.card] using FiniteField.PowerSeries.expand_card f
  have hHp : H ^ p = 1 - PowerSeries.X ^ p - 2 * F ^ p := by
    rw [← hex H]
    simp only [H, map_sub, map_mul, map_ofNat, map_one, PowerSeries.expand_X, hex F]
  have hDp : D ^ p = PowerSeries.X ^ (2 * p) - 6 * PowerSeries.X ^ p + 1 := by
    rw [← hex D]
    simp only [D, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
      PowerSeries.expand_X, ← pow_mul, mul_comm p 2]
  have hF : PowerSeries.coeff 1 F = 1 := by simp [F, hs]
  have hH : PowerSeries.coeff 1 H = -3 := by norm_num [H, hF, PowerSeries.coeff_X]
  have hHn : PowerSeries.coeff (p + 1) H = -2 * (Nat.largeSchroder p : ZMod p) := by
    simp [H, F, hs, PowerSeries.coeff_X, show p ≠ 0 from hp.ne_zero]
  have hE1 : PowerSeries.coeff 1 (D ^ (r + 1)) = -3 := by
    rw [PowerSeries.coeff_one_pow]
    have hrz : (2 : ZMod p) * (r + 1 : ℕ) = 1 := by
      have h := congrArg (fun n : ℕ => (n : ZMod p)) hpr
      push_cast at h ⊢
      rw [ZMod.natCast_self] at h
      linear_combination -h
    push_cast at hrz
    simp [D, PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
    linear_combination 3 * hrz
  have hEn : PowerSeries.coeff (p + 1) (D ^ (r + 1)) = 1 := by
    let d : Polynomial (ZMod p) := Polynomial.X ^ 2 - 6 * Polynomial.X + 1
    have hd : (d : PowerSeries (ZMod p)) = D := by
      change Polynomial.coeToPowerSeries.ringHom d = D
      simp only [d, D, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
    rw [← hd, ← Polynomial.coe_pow, Polynomial.coeff_coe]
    have hdegree : d.natDegree ≤ 2 := by
      dsimp [d]
      compute_degree
    rw [show p + 1 = (r + 1) * 2 by omega,
      Polynomial.coeff_pow_of_natDegree_le hdegree]
    simp [d, Polynomial.coeff_X, Polynomial.coeff_one]
  have hnp : ¬ p ∣ p + 1 := by
    intro h
    have h1 := (Nat.dvd_add_right (dvd_refl p)).mp h
    exact hp.ne_one (Nat.dvd_one.mp h1)
  have hFE : PowerSeries.coeff (p + 1) (F ^ p * D ^ (r + 1)) = -3 := by
    rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (F ^ p) * PowerSeries.coeff j (D ^ (r + 1)))]
    rw [sum_eq_single p]
    · simp [coeff_prime_pow p hp, Nat.div_self hp.pos, hF, hE1]
    · intro k hk hkp
      by_cases hk0 : k = 0
      · simp [hk0, coeff_prime_pow p hp, F]
      · have hnd : ¬ p ∣ k := by
          intro hd
          have hpk := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hd
          have hkp1 : k = p + 1 := by have := mem_range.mp hk; omega
          exact hnp (hkp1 ▸ hd)
        simp only [coeff_prime_pow p hp, ite_eq_right hnd, zero_mul]
    · intro hn
      exact False.elim (hn (mem_range.mpr (by omega)))
  have hl : H * (PowerSeries.X ^ (2 * p) - 6 * PowerSeries.X ^ p + 1) =
      H * PowerSeries.X ^ (2 * p) - 6 * (H * PowerSeries.X ^ p) + H := by ring
  have hrhs : (1 - PowerSeries.X ^ p - 2 * F ^ p) * D ^ (r + 1) =
      D ^ (r + 1) - PowerSeries.X ^ p * D ^ (r + 1) - 2 * (F ^ p * D ^ (r + 1)) := by ring
  have hcoef := congrArg (PowerSeries.coeff (p + 1)) hpower
  rw [hHp, hDp, hl, hrhs] at hcoef
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul] at hcoef
  rw [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_X_pow_mul'] at hcoef
  simp only [show ¬ 2 * p ≤ p + 1 by omega, ite_false, show p ≤ p + 1 by omega,
    ite_true, Nat.add_sub_cancel_left, hH, hHn, hEn, hE1, hFE] at hcoef
  have ht : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    exact fun h => Nat.not_dvd_of_pos_of_lt (by omega) hp2
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  apply (mul_left_cancel₀ ht)
  linear_combination -hcoef
private theorem not_almost_of_prime_residue (a : ℕ → ℕ) (n c : ℕ) (hn : 0 < n)
    (hc : 0 < c) (hres : ∀ p : ℕ, p.Prime → 2 < p →
      (a (n * p) : ZMod p) = (a n : ZMod p) + (c : ZMod p)) :
    ¬ IsAlmostRealizableSeq a := by
  rintro ⟨m, hm, h⟩
  obtain ⟨p, hbound, hp⟩ := Nat.exists_infinite_primes (m + c + 3)
  have : Fact p.Prime := ⟨hp⟩
  have hmz : (m : ZMod p) ≠ 0 := fun hz =>
    Nat.not_dvd_of_pos_of_lt hm (by omega) ((ZMod.natCast_eq_zero_iff m p).mp hz)
  have hcz : (c : ZMod p) ≠ 0 := fun hz =>
    Nat.not_dvd_of_pos_of_lt hc (by omega) ((ZMod.natCast_eq_zero_iff c p).mp hz)
  have he := dold_prime_zmod a m p n hp hn h
  rw [hres p hp (by omega), mul_add] at he
  have hz : (m : ZMod p) * (c : ZMod p) = 0 := by linear_combination he
  exact hcz ((mul_eq_zero.mp hz).resolve_left hmz)

/-- **The Catalan, Motzkin and large Schröder numbers are not almost realizable.** None of the
following three sequences of non-negative integers is almost realizable: the Catalan numbers
$C_n = \frac{1}{n+1}\binom{2n}{n}$, the Motzkin numbers $M(n)$, and the large Schröder numbers
$S(n)$ (OEIS A006318), given by $S(0) = 1$ and $S(n+1) = S(n) + \sum_{i=0}^{n} S(i) S(n-i)$.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Theorem 21 (`jis-2024-24.3.3-thm-21`). -/
public theorem not_isAlmostRealizableSeq_catalan_motzkin_schroder :
    ¬ IsAlmostRealizableSeq catalan ∧ ¬ IsAlmostRealizableSeq motzkinNumber ∧
      ¬ IsAlmostRealizableSeq Nat.largeSchroder := by
  refine ⟨not_almost_of_prime_residue catalan 1 1 (by decide) (by decide) ?_,
    not_almost_of_prime_residue motzkinNumber 2 1 (by decide) (by decide) ?_,
    not_almost_of_prime_residue Nat.largeSchroder 1 2 (by decide) (by decide) ?_⟩
  · intro p hp _
    norm_num only [one_mul, catalan_one, Nat.cast_one]
    exact catalan_prime_zmod p hp
  · intro p hp hp2
    norm_num only [motzkinNumber_two, Nat.cast_ofNat, Nat.cast_one]
    exact motzkin_two_prime_zmod p hp hp2
  · intro p hp hp2
    norm_num only [one_mul, Nat.largeSchroder_one, Nat.cast_ofNat]
    exact schroder_prime_zmod p hp hp2

end

end MetaMathlibExt
