/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Tactic.NormNum
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.PadovanInfiniteNotSumOfTwoPrimePowers
public import MathlibExt.NumberTheory.PadovanSequence
public import MathlibExt.NumberTheory.PerrinInfiniteNotSumOfTwoPrimePowers
public import MathlibExt.NumberTheory.PerrinSequence
public import MathlibExt.NumberTheory.ThirdOrderPrimePowers
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001
public import WantedExt.NumberTheory.GenLeonardoWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Infinitely many Tribonacci numbers are not sums of two prime powers.** Let $(T_n)_{n \ge 0}$
be the Tribonacci sequence, given by $T_0 = 0$, $T_1 = 0$, $T_2 = 1$ and
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$. There are infinitely many natural numbers $k$ such that
$T_k$ is not a sum of two prime powers.

The paper proves the stronger statement that this holds for every sufficiently large
$k \equiv 3818 \pmod{163843680}$; that form is not stated here. The paper starts the sequence
at $T_0 = 0$, $T_1 = T_2 = 1$, so its $k$-th term is $T_{k+1}$ here and it states the class as
$k \equiv 3817 \pmod{163843680}$.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 2
(`jis-2026-26.2.3-thm-2`). -/
public theorem_wanted tribonacci_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (tribonacci k : ℤ)}

/-- Infinitely many Van der Laan numbers are not a sum of two prime powers; in fact
`V_k` is not one for every sufficiently large `k ≡ 45752 (mod 967206240)`. The paper
defines `V_0 = 1`, `V_1 = 0`, `V_2 = 1`, `V_k = V_{k-2} + V_{k-3}`, which is exactly the
repository's `shiftedPadovanSequence`.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 4
(`jis-2026-26.2.3-thm-4`). -/
public theorem_wanted vanDerLaan_not_isSumOfTwoPrimePowers_of_modEq :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (shiftedPadovanSequence k : ℤ)} ∧
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k → k ≡ 45752 [MOD 967206240] →
        ¬ IsSumOfTwoPrimePowers (shiftedPadovanSequence k : ℤ)

/-- **Infinitely many Leonardo numbers are not sums of two prime powers.** Let $(L_n)_{n \ge 0}$
be the Leonardo numbers, the generalized Leonardo numbers $L_{1,n}$ with parameter $1$, given
by $L_0 = L_1 = 1$ and $L_{n+2} = L_{n+1} + L_n + 1$. There are infinitely many natural numbers
$k$ such that $L_k$ is not a sum of two prime powers.

The paper, which indexes the sequence in the same way, proves the stronger statement that this
holds for every sufficiently large $k \equiv 539073 \pmod{3543120}$; that form is not stated
here.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 6
(`jis-2026-26.2.3-thm-6`). -/
public theorem_wanted leonardo_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (genLeonardo 1 k)}

/-- Infinitely many Narayana's cows numbers (NC numbers) are not a sum of two prime powers;
in fact `N_k` is not one for every sufficiently large `k ≡ 137042 (mod 718391520)`. The paper
defines `N_0 = 0`, `N_1 = N_2 = 1`, `N_k = N_{k-1} + N_{k-3}`, which is the repository's
`narayanaCowsSequence`.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 7
(`jis-2026-26.2.3-thm-7`). -/
public theorem_wanted narayanaCows_not_isSumOfTwoPrimePowers_of_modEq :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (narayanaCowsSequence k : ℤ)} ∧
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k → k ≡ 137042 [MOD 718391520] →
        ¬ IsSumOfTwoPrimePowers (narayanaCowsSequence k : ℤ)

end

end MetaMathlibExt
