/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.NormNum
public import MathlibExt.NumberTheory.PadovanSequence
public import MathlibExt.NumberTheory.PerrinSequence
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001
public import WantedExt.NumberTheory.GenLeonardoWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Sums of two prime powers.** An integer $n$ is a sum of two prime powers if
$n = p^a + q^b$ for some primes $p$ and $q$ and some natural numbers $a$ and $b$. Since the
exponents may be $0$, the number $1 = p^0$ counts as a prime power here.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3. -/
public def IsSumOfTwoPrimePowers (n : ℤ) : Prop :=
  ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ n = (p : ℤ) ^ a + (q : ℤ) ^ b

/-- **$2$ is a sum of two prime powers.** The integer $2$ is a sum of two prime powers, since
$2 = 2^0 + 2^0$.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3. -/
public theorem isSumOfTwoPrimePowers_two : IsSumOfTwoPrimePowers 2 :=
  ⟨2, 2, 0, 0, Nat.prime_two, Nat.prime_two, by norm_num⟩

/-- **Integers below $2$ are not sums of two prime powers.** If $n$ is an integer with $n < 2$,
then $n$ is not a sum of two prime powers, since every prime power $p^a$ is at least $1$.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3. -/
public theorem not_isSumOfTwoPrimePowers_of_lt_two {n : ℤ} (hn : n < 2) :
    ¬ IsSumOfTwoPrimePowers n := by
  rintro ⟨p, q, a, b, hp, hq, rfl⟩
  have hp1 : (1 : ℤ) ≤ (p : ℤ) ^ a :=
    one_le_pow₀ (by exact_mod_cast hp.pos)
  have hq1 : (1 : ℤ) ≤ (q : ℤ) ^ b :=
    one_le_pow₀ (by exact_mod_cast hq.pos)
  omega

/-- **Infinitely many Tribonacci numbers are not sums of two prime powers.** Let $(T_n)_{n \ge 0}$
be the Tribonacci sequence, given by $T_0 = 0$, $T_1 = 0$, $T_2 = 1$ and
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$. There are infinitely many natural numbers $k$ such that
$T_k$ is not a sum of two prime powers.

The paper proves the stronger statement that this holds for every sufficiently large
$k \equiv 3817 \pmod{163843680}$. That form is not stated here, since the residue class depends
on how the sequence is indexed.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 2
(`jis-2026-26.2.3-thm-2`). -/
public theorem_wanted tribonacci_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (tribonacci k : ℤ)}

/-- **Infinitely many Padovan numbers are not sums of two prime powers.** Let $(a_n)_{n \ge 0}$ be
the shifted Padovan sequence, given by $a_0 = 1$, $a_1 = 0$, $a_2 = 1$ and
$a_{n+3} = a_{n+1} + a_n$, so that $a_{n+2} = P_n$ is the $n$-th Padovan number, where
$P_0 = P_1 = P_2 = 1$ and $P_{n+3} = P_{n+1} + P_n$. There are infinitely many natural numbers
$k$ such that $a_k$ is not a sum of two prime powers.

The paper proves the stronger statement that this holds for every sufficiently large
$k \equiv 45750 \pmod{967206240}$. That form is not stated here, since the residue class depends
on how the sequence is indexed.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 3
(`jis-2026-26.2.3-thm-3`). -/
public theorem_wanted shiftedPadovan_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (shiftedPadovanSequence k : ℤ)}

/-- **Infinitely many Perrin numbers are not sums of two prime powers.** Let $(E_n)_{n \ge 0}$ be
the Perrin sequence, given by $E_0 = 3$, $E_1 = 0$, $E_2 = 2$ and $E_{n+3} = E_{n+1} + E_n$.
There are infinitely many natural numbers $k$ such that $E_k$ is not a sum of two prime powers.

The paper proves the stronger statement that this holds for every sufficiently large
$k \equiv 472190 \pmod{967206240}$. That form is not stated here, since the residue class
depends on how the sequence is indexed.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 5
(`jis-2026-26.2.3-thm-5`). -/
public theorem_wanted perrin_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (perrinSequence k : ℤ)}

/-- **Infinitely many Leonardo numbers are not sums of two prime powers.** Let $(L_n)_{n \ge 0}$
be the Leonardo numbers, the generalized Leonardo numbers $L_{1,n}$ with parameter $1$, given
by $L_0 = L_1 = 1$ and $L_{n+2} = L_{n+1} + L_n + 1$. There are infinitely many natural numbers
$k$ such that $L_k$ is not a sum of two prime powers.

The paper proves the stronger statement that this holds for every sufficiently large
$k \equiv 539073 \pmod{3543120}$. That form is not stated here, since the residue class depends
on how the sequence is indexed.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 6
(`jis-2026-26.2.3-thm-6`). -/
public theorem_wanted leonardo_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (genLeonardo 1 k)}

/-- **Third-order recurrences with infinitely many terms not sums of two prime powers.** There
are infinitely many sequences $(s_n)_{n \ge 0}$ of positive integers with all of the following
properties: each value is taken by $s_n$ for only finitely many $n$; there are integers
$c_0, c_1, c_2$ with $c_0 \ne 0$ and $s_{n+3} = c_0 s_n + c_1 s_{n+1} + c_2 s_{n+2}$ for all
$n \ge 0$; there are no integers $d_0, d_1$ with $s_{n+2} = d_0 s_n + d_1 s_{n+1}$ for all
$n \ge 0$; and $s_k$ is not a sum of two prime powers for infinitely many $k$.

The condition that each value is taken only finitely often excludes trivial examples such as
periodic sequences taking the value $1$ infinitely often: no integer below $2$ is a sum of two
prime powers.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Corollary 1
(`jis-2026-26.2.3-cor-1`). -/
public theorem_wanted infinite_thirdOrderRecurrence_with_infinite_not_isSum :
    Set.Infinite {s : ℕ → ℕ |
      (∀ n : ℕ, 0 < s n) ∧ (∀ m : ℕ, Set.Finite {k : ℕ | s k = m}) ∧
      (∃ c : Fin 3 → ℤ, c 0 ≠ 0 ∧
        (LinearRecurrence.mk 3 c).IsSolution (fun n => (s n : ℤ))) ∧
      (¬ ∃ d : Fin 2 → ℤ,
        (LinearRecurrence.mk 2 d).IsSolution (fun n => (s n : ℤ))) ∧
      Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (s k : ℤ)}}
end

end MetaMathlibExt
