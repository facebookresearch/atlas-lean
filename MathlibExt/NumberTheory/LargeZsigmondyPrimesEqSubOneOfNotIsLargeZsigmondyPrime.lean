/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.TotientSqrtLowerBound
public import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomicPrimeMul
public import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomicProduct
public import MathlibExt.NumberTheory.PrimitiveDivisor
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring

/-!
# A non-large Zsigmondy prime satisfies `n = q - 1`

Statements from Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62.

A Zsigmondy prime for `(a, b, n)` is a primitive prime divisor of `aⁿ - bⁿ`
(`IntegerSequence.IsPrimitivePrimeDivisor`); it is large if moreover `p² ∣ aⁿ - bⁿ` or
`p > n + 1` (`MetaMathlibExt.IsLargeZsigmondyPrime`). A Zsigmondy prime that is not large
satisfies `n = q - 1` (`MetaMathlibExt.eq_sub_one_of_not_isLargeZsigmondyPrime`): primitivity
makes `n` the order of `a * b⁻¹` in `ZMod q`, so `n ∣ q - 1`, while not being large forces
`q ≤ n + 1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Large Zsigmondy prime.** Let $a$, $b$, $n$ and $p$ be natural numbers. Then $p$ is a large
Zsigmondy prime for $(a, b, n)$ when $p$ is a primitive prime divisor of the term $a^n - b^n$ of
the integer sequence $(a^m - b^m)_{m \ge 0}$, that is, $n \ge 1$, $p$ is prime, $p$ divides
$a^n - b^n$ and $p$ divides no $a^m - b^m$ with $1 \le m < n$, and moreover $p^2$ divides
$a^n - b^n$ or $p > n + 1$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 1
(definition after Theorem 1). -/
def IsLargeZsigmondyPrime (a b n p : ℕ) : Prop :=
  IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p ∧
    ((p : ℤ) ^ 2 ∣ (a : ℤ) ^ n - (b : ℤ) ^ n ∨ n + 1 < p)

-- The order argument below follows `MathlibExt.NumberTheory.BangZsigmondy`.

/-- A prime dividing $a^m - b^m$ with $m \ge 1$ cannot divide $b$ when $a$ and $b$ are coprime. -/
private theorem not_dvd_b_of_prime_dvd_sub {a b m p : ℕ} (hp : Nat.Prime p)
    (hcop : Nat.Coprime a b)
    (hdvd : (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m) (hm : 1 ≤ m) : ¬ p ∣ b := by
  intro hpb
  have hpbm : (p : ℤ) ∣ (b : ℤ) ^ m :=
    dvd_pow (Int.natCast_dvd_natCast.mpr hpb) (by omega)
  have hpam : (p : ℤ) ∣ (a : ℤ) ^ m := by
    have h := dvd_add hdvd hpbm
    rwa [sub_add_cancel] at h
  have hpa : p ∣ a ^ m := Int.natCast_dvd_natCast.mp (by simpa using hpam)
  have hpa' : p ∣ a := hp.dvd_of_dvd_pow hpa
  have hgcd : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa' hpb
  have h1 : Nat.gcd a b = 1 := hcop
  rw [h1] at hgcd
  exact hp.not_dvd_one hgcd

/-- A prime dividing $a^m - b^m$ with $m \ge 1$ cannot divide $a$ either, once it does not
divide $b$. -/
private theorem not_dvd_a_of_prime_dvd_sub {a b m p : ℕ} (hp : Nat.Prime p)
    (hdvd : (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m) (hm : 1 ≤ m)
    (hpb : ¬ p ∣ b) : ¬ p ∣ a := by
  intro hpa
  have hpam : (p : ℤ) ∣ (a : ℤ) ^ m :=
    dvd_pow (Int.natCast_dvd_natCast.mpr hpa) (by omega)
  have hpbm : (p : ℤ) ∣ (b : ℤ) ^ m := by
    have h : (b : ℤ) ^ m = (a : ℤ) ^ m - ((a : ℤ) ^ m - (b : ℤ) ^ m) := by ring
    rw [h]
    exact dvd_sub hpam hdvd
  have hpbm' : p ∣ b ^ m := Int.natCast_dvd_natCast.mp (by simpa using hpbm)
  exact hpb (hp.dvd_of_dvd_pow hpbm')

/-- For a prime $p \nmid b$, $p \mid a^m - b^m$ iff $c^m = 1$ where $c = a b^{-1}$ in `ZMod p`. -/
private theorem dvd_sub_iff_pow_eq_one {a b m p : ℕ} [Fact p.Prime] (hpb : ¬ p ∣ b) :
    (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m ↔
      ((a : ZMod p) * (b : ZMod p)⁻¹) ^ m = 1 := by
  have hb0 : (b : ZMod p) ≠ 0 := fun h => hpb ((ZMod.natCast_eq_zero_iff b p).mp h)
  have hcb : (a : ZMod p) = ((a : ZMod p) * (b : ZMod p)⁻¹) * (b : ZMod p) := by
    rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  have halg : (a : ZMod p) ^ m - (b : ZMod p) ^ m
      = (b : ZMod p) ^ m * (((a : ZMod p) * (b : ZMod p)⁻¹) ^ m - 1) := by
    conv_lhs => rw [hcb]
    rw [mul_pow, mul_sub, mul_one, mul_comm ((b : ZMod p) ^ m) _]
  have hpush : ((((a : ℤ) ^ m - (b : ℤ) ^ m : ℤ)) : ZMod p)
      = (a : ZMod p) ^ m - (b : ZMod p) ^ m := by
    push_cast
    ring
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hpush, halg, mul_eq_zero, sub_eq_zero]
  exact ⟨fun h => h.resolve_left (pow_ne_zero m hb0), Or.inr⟩

/-- The order of $a b^{-1}$ in `ZMod q` is $n$ when $q$ is a primitive prime divisor of
$a^n - b^n$. -/
private theorem orderOf_eq_of_isPrimitivePrimeDivisor {a b n q : ℕ} [Fact q.Prime]
    (hq : IntegerSequence.IsPrimitivePrimeDivisor
      (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q)
    (hqb : ¬ q ∣ b) :
    orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) = n := by
  have hn1 : 1 ≤ n := hq.one_le
  have hpow : ((a : ZMod q) * (b : ZMod q)⁻¹) ^ n = 1 :=
    (dvd_sub_iff_pow_eq_one hqb).mp hq.dvd
  have hdvd_ord : orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) ∣ n :=
    orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hle : n ≤ orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) := by
    by_contra hcon
    have hlt : orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) < n := not_le.mp hcon
    rcases Nat.eq_zero_or_pos (orderOf ((a : ZMod q) * (b : ZMod q)⁻¹)) with h0 | hpos
    · rw [h0, zero_dvd_iff] at hdvd_ord
      omega
    · have h1 : ((a : ZMod q) * (b : ZMod q)⁻¹) ^ orderOf _ = 1 :=
        pow_orderOf_eq_one _
      have hdvd' : (q : ℤ) ∣ (a : ℤ) ^ orderOf _ - (b : ℤ) ^ orderOf _ :=
        (dvd_sub_iff_pow_eq_one hqb).mpr h1
      exact hq.not_dvd_of_lt hpos hlt hdvd'
  exact le_antisymm (Nat.le_of_dvd (by omega) hdvd_ord) hle

/-- A primitive prime divisor $q$ of $a^n - b^n$ with $a$ coprime to $b$ satisfies $n \mid q-1$. -/
private theorem dvd_sub_one_of_isPrimitivePrimeDivisor {a b n q : ℕ}
    (hcop : a.Coprime b)
    (hq : IntegerSequence.IsPrimitivePrimeDivisor
      (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q) :
    n ∣ q - 1 := by
  have hprime : q.Prime := hq.prime
  have : Fact q.Prime := ⟨hprime⟩
  have hqb : ¬ q ∣ b :=
    not_dvd_b_of_prime_dvd_sub hprime hcop hq.dvd hq.one_le
  have hqa : ¬ q ∣ a :=
    not_dvd_a_of_prime_dvd_sub hprime hq.dvd hq.one_le hqb
  have hord : orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) = n :=
    orderOf_eq_of_isPrimitivePrimeDivisor hq hqb
  have hc0 : (a : ZMod q) * (b : ZMod q)⁻¹ ≠ 0 :=
    mul_ne_zero (fun h => hqa ((ZMod.natCast_eq_zero_iff a q).mp h))
      (inv_ne_zero (fun h => hqb ((ZMod.natCast_eq_zero_iff b q).mp h)))
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one hc0

set_option linter.unusedVariables false in
/-- **A Zsigmondy prime $q$ that is not large satisfies $n = q - 1$.** Let $a > b$ be coprime
positive integers and let $n \ge 2$. If $q$ is a primitive prime divisor of the term $a^n - b^n$
of the integer sequence $(a^m - b^m)_{m \ge 0}$ and $q$ is not a large Zsigmondy prime for
$(a, b, n)$, then $n = q - 1$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 6. -/
theorem eq_sub_one_of_not_isLargeZsigmondyPrime {a b n q : ℕ} (hb : 0 < b)
    (hba : b < a) (hcop : a.Coprime b) (hn : 2 ≤ n)
    (hq : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q)
    (hql : ¬ IsLargeZsigmondyPrime a b n q) :
    n = q - 1 := by
  have hle : q ≤ n + 1 := not_lt.mp fun h => hql ⟨hq, Or.inr h⟩
  have hdvd : n ∣ q - 1 := dvd_sub_one_of_isPrimitivePrimeDivisor hcop hq
  have hnpos : 0 < q - 1 := by
    have hq2 : 2 ≤ q := hq.prime.two_le
    omega
  have hnle : n ≤ q - 1 := Nat.le_of_dvd hnpos hdvd
  exact le_antisymm hnle (by omega)

end

end MetaMathlibExt
