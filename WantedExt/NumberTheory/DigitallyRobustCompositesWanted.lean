/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

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

/--
**Infinitely many digitally robust composites.** There are infinitely many natural numbers that
are digitally robust composites: composite numbers coprime to $10$ that stay composite after
replacing any one base-ten digit (including a leading zero) by a different digit, after deleting
any one of their digits, and after inserting any digit in any position.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem_wanted infinitelyMany_digitallyRobustComposites :
    {N : ℕ | IsDigitallyRobustComposite N}.Infinite

/--
**Prime divisors of cyclotomic values at 10.** Let $b$ be a positive integer, let $\Phi_b$ be
the $b$-th cyclotomic polynomial with integer coefficients, and let $p$ be a prime that divides
the integer $\Phi_b(10)$. If $b < p$, then the multiplicative order of $10$ modulo $p$ is $b$.
If $p \le b$ and $b > 2$, then $p$ divides $b$, every prime divisor $q$ of $b$ satisfies
$q \le p$ (so $p$ is the largest prime divisor of $b$), and $p^2$ does not divide $\Phi_b(10)$.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Lemma 1.
-/
public theorem_wanted cyclotomicPrimeDivisor_order_and_largestPrime :
    ∀ (b p : ℕ), 0 < b → p.Prime →
      (p : ℤ) ∣ (Polynomial.cyclotomic b ℤ).eval 10 →
        (b < p → orderOf (10 : ZMod p) = b) ∧
          (p ≤ b → 2 < b → p ∣ b ∧
            (∀ q, q.Prime → q ∣ b → q ≤ p) ∧
              ¬ (p : ℤ) ^ 2 ∣ (Polynomial.cyclotomic b ℤ).eval 10)

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
