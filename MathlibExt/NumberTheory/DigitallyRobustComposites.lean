/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic.NormNum.Prime

/-!
# Digitally robust composite numbers

This module defines the three base-ten digit edits and proves the order and multiplicity
properties of prime divisors of cyclotomic values at ten.
-/

namespace MetaMathlibExt

@[expose] public section

/--
**Replacing a base-ten digit.** For natural numbers $N$, $i$ and $d$, the result of replacing the
digit of $N$ at position $i$ by $d$ is the natural number
$$\lfloor N / 10^{i+1} \rfloor \cdot 10^{i+1} + d \cdot 10^i + (N \bmod 10^i).$$
Positions are counted from the units digit, which is position $0$, and positions beyond the
written numeral are leading zeros. When $d < 10$, this keeps every digit of $N$ other than the
one at position $i$ and puts $d$ there.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public def replaceDigit (N i d : ℕ) : ℕ :=
  N / 10 ^ (i + 1) * 10 ^ (i + 1) + d * 10 ^ i + N % 10 ^ i

/--
**Deleting a digit.** For natural numbers $N$ and $i$, deleting the base-ten digit of $N$ in
position $i$, where positions are counted from $0$ at the units digit, gives the number

$$\lfloor N / 10^{i+1} \rfloor \cdot 10^{i} + (N \bmod 10^{i}),$$

so the digits above position $i$ move down one place and the digits below position $i$ stay
where they are.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public def deleteDigit (N i : ℕ) : ℕ :=
  N / 10 ^ (i + 1) * 10 ^ i + N % 10 ^ i

/--
**Inserting a digit.** For natural numbers $N$, $i$ and $d$, inserting $d$ into the base-ten
expansion of $N$ in position $i$, where positions are counted from $0$ at the units digit, gives
the number

$$\lfloor N / 10^{i} \rfloor \cdot 10^{i+1} + d \cdot 10^{i} + (N \bmod 10^{i}),$$

so the digits in positions $i$ and above move up one place, $d$ takes position $i$, and the
digits below position $i$ stay where they are. For $i = 0$ this appends $d$ on the right, and
for $i$ at least the number of digits of $N$ it inserts $d$ among the leading zeros.

When $i$ equals the number of digits of $N$, inserting $d$ gives the same number as replacing
the first leading zero by $d$.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public def insertDigit (N i d : ℕ) : ℕ :=
  N / 10 ^ i * 10 ^ (i + 1) + d * 10 ^ i + N % 10 ^ i

/--
**Digitally robust composite numbers.** A natural number $N$ is a digitally robust composite if
it is composite (greater than $1$ and not prime), coprime to $10$, and each of the following
numbers is greater than $1$ and not prime: the result of replacing the base-ten digit of $N$ in
any position $i$ by any digit $d < 10$ other than $\lfloor N / 10^{i} \rfloor \bmod 10$; the
result of deleting the single digit in any position $i$ smaller than the number of base-ten
digits of $N$; and the result of inserting any digit $d < 10$ in any position $i$. Positions are
counted from $0$ at the units digit, and positions beyond the written digits of $N$ refer to its
leading zeros.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public def IsDigitallyRobustComposite (N : ℕ) : Prop :=
  (1 < N ∧ ¬ N.Prime) ∧
    Nat.Coprime N 10 ∧
      (∀ i d, d < 10 → d ≠ N / 10 ^ i % 10 →
        1 < replaceDigit N i d ∧ ¬ (replaceDigit N i d).Prime) ∧
        (∀ i < (Nat.digits 10 N).length,
          1 < deleteDigit N i ∧ ¬ (deleteDigit N i).Prime) ∧
          ∀ i d, d < 10 → 1 < insertDigit N i d ∧ ¬ (insertDigit N i d).Prime

open Polynomial

-- For b = d * p, the cyclotomic value divides the p-term geometric sum at 10^d.
-- When 10^d is 1 modulo the odd prime p, this sum has multiplicity exactly one.
private theorem sq_not_dvd_cyclotomic_eval {d p : ℕ} (hd : 0 < d) (hp : p.Prime)
    (hodd : Odd p) (hpow : (10 : ZMod p) ^ d = 1) :
    ¬ (p : ℤ) ^ 2 ∣ (cyclotomic (d * p) ℤ).eval 10 := by
  have : Fact p.Prime := ⟨hp⟩
  let x := (10 : ℤ) ^ d
  have hproper : d ∈ (d * p).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨dvd_mul_right .., lt_mul_of_one_lt_right hd hp.one_lt⟩
  have hdiv : (x - 1) * (cyclotomic (d * p) ℤ).eval 10 ∣ x ^ p - 1 := by
    simpa [x, pow_mul] using eval_dvd (x := (10 : ℤ))
      (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hproper)
  have hx : 1 < x := one_lt_pow₀ (by decide : 1 < (10 : ℤ)) hd.ne'
  rw [← mul_geom_sum x p, mul_dvd_mul_iff_left (sub_ne_zero.mpr hx.ne')] at hdiv
  have hsub : (p : ℤ) ∣ x - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [x, hpow]
  have hunit : ¬ (p : ℤ) ∣ x := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [x, hpow]
  have hmult : emultiplicity (p : ℤ) (∑ i ∈ Finset.range p, x ^ i) = 1 := by
    simpa using emultiplicity_geom_sum₂_eq_one (Nat.prime_iff_prime_int.mp hp) hodd hsub hunit
  exact fun hsq => ((emultiplicity_eq_coe (n := 1)).mp hmult).2 (hsq.trans hdiv)

/--
**Prime divisors of cyclotomic values at 10.** Let $b$ be a positive integer, let $\Phi_b$ be
the $b$-th cyclotomic polynomial with integer coefficients, and let $p$ be a prime that divides
the integer $\Phi_b(10)$. If $b < p$, then the multiplicative order of $10$ modulo $p$ is $b$.
If $p \le b$ and $b > 2$, then $p$ divides $b$, every prime divisor $q$ of $b$ satisfies
$q \le p$ (so $p$ is the largest prime divisor of $b$), and $p^2$ does not divide $\Phi_b(10)$.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Lemma 1.
-/
public theorem cyclotomicPrimeDivisor_order_and_largestPrime :
    ∀ (b p : ℕ), 0 < b → p.Prime →
      (p : ℤ) ∣ (Polynomial.cyclotomic b ℤ).eval 10 →
        (b < p → orderOf (10 : ZMod p) = b) ∧
          (p ≤ b → 2 < b → p ∣ b ∧
            (∀ q, q.Prime → q ∣ b → q ≤ p) ∧
              ¬ (p : ℤ) ^ 2 ∣ (Polynomial.cyclotomic b ℤ).eval 10) := by
  intro b p hb hp hdvd
  have : Fact p.Prime := ⟨hp⟩
  have hroot : (cyclotomic b (ZMod p)).IsRoot 10 := by
    simpa [IsRoot.def] using
      (cyclotomic.eval_apply (10 : ℤ) b (Int.castRingHom (ZMod p))).trans
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd)
  obtain ⟨k, m, hpm, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb.ne' p hp.ne_one
  have : NeZero (m : ZMod p) := NeZero.of_not_dvd (ZMod p) hpm
  have hprim : IsPrimitiveRoot (10 : ZMod p) m :=
    isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp (hbm ▸ hroot)
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h => hpm (h ▸ dvd_zero p))
  have hten := hprim.ne_zero hm.ne'
  have hmlt : m < p := by
    have hdiv := ZMod.orderOf_dvd_card_sub_one hten
    rw [← hprim.eq_orderOf] at hdiv
    exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hdiv).trans_lt (Nat.pred_lt hp.ne_zero)
  cases k with
  | zero =>
    simp only [pow_zero, one_mul] at hbm
    subst b
    exact ⟨fun _ => hprim.eq_orderOf.symm, fun h => (hmlt.not_ge h).elim⟩
  | succ k =>
    have hb' : b = (m * p ^ k) * p := by
      rw [hbm, pow_succ]
      ac_rfl
    have hpb : p ∣ b := hb' ▸ dvd_mul_left ..
    refine ⟨fun h => (h.not_ge (Nat.le_of_dvd hb hpb)).elim, fun _ _ => ⟨hpb, ?_, ?_⟩⟩
    · intro q hq hqb
      rw [hbm] at hqb
      rcases hq.dvd_mul.mp hqb with hqpow | hqm
      · exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqpow)).le
      · exact (Nat.le_of_dvd hm hqm).trans hmlt.le
    · have hodd : Odd p := hp.odd_of_ne_two (by
        rintro rfl
        exact hten (by rfl))
      rw [hb']
      apply sq_not_dvd_cyclotomic_eval (Nat.mul_pos hm (pow_pos hp.pos _)) hp hodd
      rw [pow_mul, hprim.pow_eq_one, one_pow]

/--
**Replacing the units digit of 25011 by 3.** Replacing the base-ten digit of $25011$ at
position $0$, its units digit, by $3$ gives $25013$.

This is a sample computation illustrating the replacement operation of Theorem 1, not a claim
from the theorem.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem replaceDigit_25011_units : replaceDigit 25011 0 3 = 25013 := by
  norm_num [replaceDigit]

/--
**Deleting the ten-thousands digit of 25011.** Deleting the base-ten digit in position $4$ of
$25011$, where positions are counted from $0$ at the units digit (so position $4$ is the
ten-thousands digit $2$), gives $5011$.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem deleteDigit_25011_tenThousands : deleteDigit 25011 4 = 5011 := by
  norm_num [deleteDigit]

/--
**Inserting a digit among the leading zeros of 25011.** Inserting the digit $1$ in position $7$
of $25011$, where positions are counted from $0$ at the units digit (so the new digit goes
between the second and third leading zeros), gives $10025011$.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem insertDigit_25011_leadingZeros : insertDigit 25011 7 1 = 10025011 := by
  norm_num [insertDigit]

/--
**Replacing a leading zero of 25011 by zero.** Replacing the base-ten digit in position $6$ of
$25011$, where positions are counted from $0$ at the units digit (so this digit is a leading
zero), by $0$ gives $25011$ again.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem replaceDigit_25011_leadingZero : replaceDigit 25011 6 0 = 25011 := by
  norm_num [replaceDigit]

/--
**Base-ten digits are less than ten.** For all natural numbers $N$ and $i$, the base-ten digit
of $N$ in position $i$ (counted from $0$ at the units digit), namely
$\lfloor N / 10^{i} \rfloor \bmod 10$, is less than $10$.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem digitValue_lt_ten (N i : ℕ) : N / 10 ^ i % 10 < 10 := by
  exact Nat.mod_lt _ (by norm_num)

/--
**25011 is not a digitally robust composite.** The number $25011$ is not a digitally robust
composite: replacing its units digit $1$ by $3$ gives the prime $25013$.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem not_isDigitallyRobustComposite_25011 : ¬ IsDigitallyRobustComposite 25011 := by
  intro h
  obtain ⟨_, _, hreplace, _, _⟩ := h
  have hcomposite := hreplace 0 3 (by norm_num) (by norm_num)
  rw [replaceDigit_25011_units] at hcomposite
  exact hcomposite.2 (by norm_num)

end

end MetaMathlibExt
