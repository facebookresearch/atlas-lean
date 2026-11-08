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

/-- Representability as a sum of two prime powers: `n = p ^ a + q ^ b`
for primes `p, q` and nonnegative exponents `a, b` (so `1` counts as a
prime power, via exponent `0`).

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3. -/
public def IsSumOfTwoPrimePowers (n : ℤ) : Prop :=
  ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ n = (p : ℤ) ^ a + (q : ℤ) ^ b

/-- Characteristic example: `2 = 2 ^ 0 + 2 ^ 0` is representable.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3. -/
public theorem isSumOfTwoPrimePowers_two : IsSumOfTwoPrimePowers 2 :=
  ⟨2, 2, 0, 0, Nat.prime_two, Nat.prime_two, by norm_num⟩

/-- Characteristic threshold: no integer below `2` is representable,
since each prime power is at least `1`.

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

/-- Infinitely many Tribonacci numbers are not a sum of two prime
powers. Stated for the repository Tribonacci sequence with initial
values `0, 0, 1` (OEIS A000073). The paper's strengthening to every
sufficiently large `k ≡ 3817 (mod 163843680)` is omitted: the extracted
statement does not display the paper's seed convention, and the
residue class depends on it.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 2
(`jis-2026-26.2.3-thm-2`). -/
public theorem_wanted tribonacci_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (tribonacci k : ℤ)}

/-- Infinitely many Padovan numbers are not a sum of two prime powers.
Stated for the repository shifted Padovan sequence (`1, 0, 1`, with
`shiftedPadovanSequence (n + 2)` equal to the standard Padovan number
`P_n` with initial values `1, 1, 1`), so the infinitude content agrees
with the paper's. The paper's strengthening to every sufficiently
large `k ≡ 45750 (mod 967206240)` is omitted for the same
seed-convention reason as in the Tribonacci statement.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 3
(`jis-2026-26.2.3-thm-3`). -/
public theorem_wanted shiftedPadovan_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (shiftedPadovanSequence k : ℤ)}

/-- Infinitely many Perrin numbers are not a sum of two prime powers.
Stated for the repository Perrin sequence with initial values
`3, 0, 2`. The paper's strengthening to every sufficiently large
`k ≡ 472190 (mod 967206240)` is omitted for the same seed-convention
reason as in the Tribonacci statement.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 5
(`jis-2026-26.2.3-thm-5`). -/
public theorem_wanted perrin_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (perrinSequence k : ℤ)}

/-- Infinitely many Leonardo numbers are not a sum of two prime
powers. The ordinary Leonardo numbers are the specialization
`genLeonardo 1` of the repository's generalized Leonardo API.
The paper's strengthening to every sufficiently large
`k ≡ 539073 (mod 3543120)` is omitted for the same seed-convention
reason as in the Tribonacci statement.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 6
(`jis-2026-26.2.3-thm-6`). -/
public theorem_wanted leonardo_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (genLeonardo 1 k)}

/-- There are infinitely many degree-three linear homogeneous
recurrence sequences of positive integers taking each positive
integer value only finitely often, each having infinitely many
terms that are not a sum of two prime powers. Degree three is
encoded using Mathlib's `LinearRecurrence` API: `fun n => (s n : ℤ)`
is a solution of an order-three recurrence whose coefficient of the
oldest term (`c 0`) is nonzero, but is not a solution of any
order-two recurrence. The positivity and fiber-finiteness
conditions exclude degenerate families such as the constant
negative sequences, which would otherwise satisfy the conclusion
for unrelated reasons (every term below `2` is nonrepresentable).

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
