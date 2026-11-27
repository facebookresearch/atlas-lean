/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HigherANumbersPeriodicSum
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Periodicity of floors of rational multiples of prime powers

The definitions `primeToPDen`, `primeToPNum`, `basePPeriod`, and `basePDelay` describe the
prime-to-`p` parts and the period and delay of a rational number. The theorem
`floor_mul_pow_modEq` proves periodicity of its scaled floors modulo the prime-to-`p`
numerator and modulo `p`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 7. Statements follow the arXiv text (arXiv:2407.13969v3).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Prime-to-$p$ part of the denominator.** For a natural number $p$ and a rational number
$x$ whose denominator in lowest terms is $b \ge 1$, $x_D$ is the natural number $b / p^k$, where
$p^k$ is the largest power of $p$ dividing $b$ (with $k = 0$ when $p = 1$).

For a prime $p$ and $x > 0$ this gives $x = p^{v_p(x)} x_N / x_D$ with $x_N$ and $x_D$ coprime to
$p$, where $x_N$ is the prime-to-$p$ part of the numerator (Notation 2).

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 2 (`x_D`). -/
def primeToPDen (p : ℕ) (x : ℚ) : ℕ := x.den / p ^ padicValNat p x.den

/-- **Prime-to-$p$ part of the numerator.** For a natural number $p$ and a rational number $x$
whose numerator in lowest terms is $a$, $x_N$ is the natural number $|a| / p^k$, where $p^k$ is
the largest power of $p$ dividing $|a|$, with $k = 0$ when $p = 1$ or $a = 0$. In particular
$x_N = 0$ when $x = 0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 2 (`x_N`). -/
def primeToPNum (p : ℕ) (x : ℚ) : ℕ := x.num.natAbs / p ^ padicValNat p x.num.natAbs

/-- **Period of the base-$p$ expansion.** For a natural number $p$ and a rational number $x$, let
$x_D$ be the denominator of $x$ in lowest terms divided by the largest power of $p$ dividing it.
The period $L_x$ of the base-$p$ expansion of $x$ is the multiplicative order of $p$ modulo $x_D$:
the least $n \ge 1$ with $p^n \equiv 1 \pmod{x_D}$, or $0$ if there is no such $n$. For prime $p$
this is the order of $p$ in $(\mathbb{Z}/x_D\mathbb{Z})^\times$.

For prime $p$ and $x > 0$, Lemma 2 of the source identifies $L_x$ with the minimal period of the
base-$p$ digits of $x$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `L_x` and Lemma 2. -/
noncomputable def basePPeriod (p : ℕ) (x : ℚ) : ℕ := orderOf (p : ZMod (primeToPDen p x))

/-- **Delay of the base-$p$ expansion.** For a natural number $p$ and a rational number $x$, the
delay of the base-$p$ expansion of $x$ is $D_x = -v_p(x)$, where $v_p$ is the $p$-adic valuation
(with $v_p(0) = 0$).

For prime $p$ and $x > 0$, Lemma 2 of the source identifies $D_x$ with the minimal delay of the
base-$p$ digits of $x$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `D_x` and Lemma 2. -/
noncomputable def basePDelay (p : ℕ) (x : ℚ) : ℤ := -padicValRat p x

private lemma primeToPDen_mul_pow (p : ℕ) (x : ℚ) :
    primeToPDen p x * p ^ padicValNat p x.den = x.den := by
  exact Nat.div_mul_cancel (by
    simpa only [Nat.padicValNat_def] using pow_multiplicity_dvd p x.den)

private lemma primeToPNum_mul_pow (p : ℕ) (x : ℚ) :
    primeToPNum p x * p ^ padicValNat p x.num.natAbs = x.num.natAbs := by
  exact Nat.div_mul_cancel (by
    simpa only [Nat.padicValNat_def] using pow_multiplicity_dvd p x.num.natAbs)

private lemma rational_primeToP_parts (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : 0 < x) :
    x = (primeToPNum p x : ℚ) / primeToPDen p x * (p : ℚ) ^ (-basePDelay p x) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hnum : (x.num.natAbs : ℚ) = x.num := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (Rat.num_pos.mpr hx).le]
  rw [basePDelay, neg_neg, padicValRat_def]
  simp only [padicValInt, ← Nat.padicValNat_def]
  rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast, div_mul_div_comm,
    ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul,
    primeToPNum_mul_pow, primeToPDen_mul_pow, hnum, Rat.num_div_den]

private lemma primeToPDen_ne_zero (p : ℕ) (x : ℚ) : primeToPDen p x ≠ 0 := by
  intro h
  have hd := primeToPDen_mul_pow p x
  rw [h, zero_mul] at hd
  exact (Rat.den_pos x).ne' hd.symm

private lemma period_dvd_sub_one (p : ℕ) (x : ℚ) :
    (primeToPDen p x : ℤ) ∣ (p : ℤ) ^ basePPeriod p x - 1 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one, sub_eq_zero,
    basePPeriod] using pow_orderOf_eq_one (p : ZMod (primeToPDen p x))

private lemma scaled_rational (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : 0 < x) (n : ℤ) :
    x * (p : ℚ) ^ n = (primeToPNum p x : ℚ) / primeToPDen p x *
      (p : ℚ) ^ (n - basePDelay p x) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  conv_lhs => rw [rational_primeToP_parts p hx]
  rw [mul_assoc, ← zpow_add₀ hp]
  congr 2
  omega

private lemma floor_period_difference (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : 0 < x)
    {n : ℤ} (hn : basePDelay p x ≤ n) :
    ∃ t : ℤ, ⌊x * (p : ℚ) ^ (n + basePPeriod p x)⌋ = ⌊x * (p : ℚ) ^ n⌋ +
      (primeToPNum p x : ℤ) * (p : ℤ) ^ (n - basePDelay p x).toNat * t := by
  obtain ⟨t, ht⟩ := period_dvd_sub_one p x
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hb : (primeToPDen p x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (primeToPDen_ne_zero p x)
  have hk : ((n - basePDelay p x).toNat : ℤ) = n - basePDelay p x :=
    Int.toNat_of_nonneg (by omega)
  have ht' : (p : ℚ) ^ basePPeriod p x = (primeToPDen p x : ℚ) * t + 1 := by
    exact_mod_cast (sub_eq_iff_eq_add.mp ht)
  refine ⟨t, ?_⟩
  have hq : x * (p : ℚ) ^ (n + basePPeriod p x) = x * (p : ℚ) ^ n +
      (((primeToPNum p x : ℤ) * (p : ℤ) ^ (n - basePDelay p x).toNat * t : ℤ) : ℚ) := by
    rw [scaled_rational p hx, scaled_rational p hx, ← sub_add_eq_add_sub,
      ← hk, zpow_add₀ hp, zpow_natCast, zpow_natCast, ht']
    push_cast
    simp only [Int.toNat_natCast]
    field_simp [hb]
    ring
  rw [hq, Int.floor_add_intCast]

/-- **Periodicity of $\lfloor x p^n \rfloor$ modulo $x_N$ and modulo $p$.** Let $p$ be a prime and
$x$ a positive rational. Write $x_N$ for the prime-to-$p$ part of the numerator of $x$,
$D_x = -v_p(x)$ for the delay of its base-$p$ expansion, and $L_x$ for its period, the order of
$p$ modulo the prime-to-$p$ part of the denominator of $x$. Then for every integer $n$:
(i) if $n \ge D_x$, then $\lfloor x p^n \rfloor \equiv \lfloor x p^{n + L_x} \rfloor \pmod{x_N}$;
(ii) if $n \ge D_x + 1$, then $\lfloor x p^n \rfloor \equiv \lfloor x p^{n + L_x} \rfloor \pmod p$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 7 (`integers-2026-A78-lem-7`). -/
public theorem floor_mul_pow_modEq (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : 0 < x) :
    (∀ n : ℤ, basePDelay p x ≤ n →
        ⌊x * (p : ℚ) ^ n⌋ ≡ ⌊x * (p : ℚ) ^ (n + basePPeriod p x)⌋ [ZMOD primeToPNum p x]) ∧
      (∀ n : ℤ, basePDelay p x + 1 ≤ n →
        ⌊x * (p : ℚ) ^ n⌋ ≡ ⌊x * (p : ℚ) ^ (n + basePPeriod p x)⌋ [ZMOD p]) := by
  constructor
  · intro n hn
    obtain ⟨t, ht⟩ := floor_period_difference p hx hn
    apply Int.modEq_iff_dvd.mpr
    refine ⟨(p : ℤ) ^ (n - basePDelay p x).toNat * t, ?_⟩
    rw [ht]
    ring
  · intro n hn
    obtain ⟨t, ht⟩ := floor_period_difference p hx (by omega : basePDelay p x ≤ n)
    have hk : (n - basePDelay p x).toNat ≠ 0 := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk
    apply Int.modEq_iff_dvd.mpr
    refine ⟨(primeToPNum p x : ℤ) * (p : ℤ) ^ k * t, ?_⟩
    rw [ht, hk, pow_succ]
    ring

end

end MetaMathlibExt
