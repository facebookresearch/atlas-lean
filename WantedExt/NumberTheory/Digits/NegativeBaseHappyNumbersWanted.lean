/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Function.Iterate
public import MathlibExt.NumberTheory.Digits.NegativeBaseDigitSquareCongruence
public import MathlibExt.NumberTheory.Digits.NegativeBaseHappyNumbers

/-!
# Negative base happy numbers

Statements from Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The
Fibonacci Quarterly 62 (2024), no. 2, 125–129.

For `b ≤ -2` every integer `a` has a unique expansion `a = ∑_{i=0}^n a_i b^i` with digits
`0 ≤ a_i ≤ |b| - 1`, and `S_{2,b}(a) = ∑ a_i²`. An integer `a` is `b`-happy if `S_{2,b}^k(a) = 1`
for some `k ≥ 1`. `U_{2,b}` is the set of positive integers lying on a cycle of `S_{2,b}`, and a
finite set `T` is `(2, b)`-good if for each `u ∈ U_{2,b}` there are `n, k ≥ 1` with
`S_{2,b}^k(t + n) = u` for all `t ∈ T`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The digit-square sum of a single digit.** Let $b$ and $d$ be integers with $0 < d < -b$, so
that $b \le -2$ and $d$ is a nonzero base-$b$ digit. Then the base-$b$ digit-square sum $S_{2,b}$
satisfies $S_{2,b}(d) = d^2$.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
theorem negBaseSqDigitSum_of_digit {b d : ℤ} (hd0 : 0 < d) (hd : d < -b) :
    negBaseSqDigitSum b d = d ^ 2 := by
  have hmod : d % b = d := by
    rw [← Int.emod_neg]
    exact Int.emod_eq_of_lt hd0.le hd
  unfold negBaseSqDigitSum
  rw [show 2 * d.natAbs + 2 = (2 * d.natAbs + 1) + 1 from rfl, negBaseSqDigitSumAux]
  simp only [hd0.ne', ↓reduceIte, hmod, sub_self, Int.zero_ediv]
  cases 2 * d.natAbs + 1 <;> simp [negBaseSqDigitSumAux]

/-- **Sample values of the negative-base digit-square sum.** Write $S_{2,b}$ for the base-$b$
digit-square sum, which sends an integer to the sum of the squares of its base-$b$ digits. Then
$S_{2,-10}(-1) = 82$, $S_{2,-10}(10) = 82$ and $S_{2,-4}(5) = 11$. Indeed $-1 = 1 \cdot (-10) + 9$
and $10 = 1 \cdot (-10)^2 + 9 \cdot (-10) + 0$ have base-$(-10)$ digits $1, 9$ and $1, 9, 0$, and
$5 = 1 \cdot (-4)^2 + 3 \cdot (-4) + 1$ has base-$(-4)$ digits $1, 3, 1$ (most significant first).

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
theorem negBaseSqDigitSum_samples :
    negBaseSqDigitSum (-10) (-1) = 82 ∧ negBaseSqDigitSum (-10) 10 = 82 ∧
      negBaseSqDigitSum (-4) 5 = 11 := by
  decide

/-- **Happy integers in a negative base.** Let $b$ be an integer and let $S_{2,b}$ be the
base-$b$ digit-square sum, which for $b \le -2$ sends an integer to the sum of the squares of its
base-$b$ digits. An integer $a$ is $b$-happy if $S_{2,b}^k(a) = 1$ for some $k \ge 1$, where
$S_{2,b}^k$ denotes the $k$-th iterate of $S_{2,b}$.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
def IsNegBaseHappy (b a : ℤ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (negBaseSqDigitSum b)^[k] a = 1

/-- **$1$ is happy in every negative base.** For every integer $b \le -2$, the integer $1$ is
$b$-happy.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
theorem isNegBaseHappy_one {b : ℤ} (hb : b ≤ -2) : IsNegBaseHappy b 1 :=
  ⟨1, one_pos, by
    simpa using negBaseSqDigitSum_of_digit (b := b) (d := 1) one_pos (by omega)⟩

/-- **One lies on a cycle of the negative-base digit-square map.** For every integer $b \le -2$,
$1 \in U_{2,b}$, where $U_{2,b}$ is the set of positive integers lying on a cycle of the base-$b$
digit-square sum $S_{2,b}$.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
theorem one_mem_negBaseSqDigitCycles {b : ℤ} (hb : b ≤ -2) : (1 : ℤ) ∈ negBaseSqDigitCycles b :=
  ⟨one_pos, isNegBaseHappy_one hb⟩

/-- **Happy numbers in base $-2$.** There is an integer $n$ such that $n + 3i$ is $(-2)$-happy for
every natural number $i$, and an integer $a$ is $(-2)$-happy if and only if $a \equiv 1 \pmod 3$.

This is part (1) of the Grundman–Harris theorem.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.1. -/
public theorem_wanted isNegBaseHappy_neg_two_iff :
    (∃ n : ℤ, ∀ i : ℕ, IsNegBaseHappy (-2) (n + 3 * i)) ∧
      ∀ a : ℤ, IsNegBaseHappy (-2) a ↔ a ≡ 1 [ZMOD 3]

/-- **Happy numbers in base $-3$.** There is an integer $n$ such that $n + 2i$ is $(-3)$-happy for
every natural number $i$, and an integer $a$ is $(-3)$-happy if and only if $a \equiv 1 \pmod 2$.

This is part (2) of the Grundman–Harris theorem.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.1. -/
public theorem_wanted isNegBaseHappy_neg_three_iff :
    (∃ n : ℤ, ∀ i : ℕ, IsNegBaseHappy (-3) (n + 2 * i)) ∧
      ∀ a : ℤ, IsNegBaseHappy (-3) a ↔ a ≡ 1 [ZMOD 2]

/-- **Arbitrarily long runs of consecutive happy numbers in bases $-4$, $-6$, $-8$, $-10$.** Let
$b \in \{-4, -6, -8, -10\}$. For every natural number $N$ there is an integer $n$ such that
$n + i$ is $b$-happy for every $0 \le i < N$.

This is part (3) of the Grundman–Harris theorem.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.1. -/
public theorem_wanted isNegBaseHappy_consecutive_runs_small (b : ℤ)
    (hb : b = -4 ∨ b = -6 ∨ b = -8 ∨ b = -10) (N : ℕ) :
    ∃ n : ℤ, ∀ i < N, IsNegBaseHappy b (n + i)

/-- **Arithmetic progressions of happy numbers in odd negative bases.** Let $b \le -3$ be an odd
integer. For every natural number $N$ there is an integer $n$ such that $n + 2i$ is $b$-happy for
every natural number $i < N$. Thus there are arbitrarily long finite arithmetic progressions with
common difference $2$ of $b$-happy integers.

This is part (4) of the theorem of Grundman and Harris.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.1. -/
public theorem_wanted isNegBaseHappy_two_consecutive_runs_odd (b : ℤ) (hb : b ≤ -3)
    (hodd : Odd b) (N : ℕ) :
    ∃ n : ℤ, ∀ i < N, IsNegBaseHappy b (n + 2 * i)

/-- **Arbitrarily long runs of consecutive happy numbers in even bases at most $-4$.** Let
$b \le -4$ be an even integer. For every natural number $N$ there is an integer $n$ such that
$n + i$ is $b$-happy for every $0 \le i < N$.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 1.2. -/
public theorem_wanted isNegBaseHappy_consecutive_runs_even (b : ℤ) (hb : b ≤ -4) (heven : Even b)
    (N : ℕ) :
    ∃ n : ℤ, ∀ i < N, IsNegBaseHappy b (n + i)

/-- **Even bases at most $-4$ make every finite set of positive integers good.** Let $b \le -4$
be an even integer. Then every finite set of positive integers is $(2, b)$-good.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Theorem 3.2. -/
public theorem_wanted isNegBaseGood_of_even (b : ℤ) (hb : b ≤ -4) (heven : Even b) (T : Finset ℤ)
    (hT : ∀ t ∈ T, 0 < t) :
    IsNegBaseGood b T

end

end MetaMathlibExt
