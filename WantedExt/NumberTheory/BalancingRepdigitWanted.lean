/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

namespace MetaMathlibExt

@[expose] public section

/-- **Balancing numbers.** The balancing numbers are the integers $B_n$ for $n \in \mathbb{N}$
defined by $B_0 = 0$, $B_1 = 1$ and $B_{n+2} = 6 B_{n+1} - B_n$ for all $n$.

Source: standard definition used in "Balancing and Lucas-Balancing Numbers as
the Difference of Two Repdigits" (Integers 2025, A15); the values
`B_2 = 6`, `B_3 = 35` are those displayed in its Theorem 2. -/
public def balancingNum : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 6 * balancingNum (n + 1) - balancingNum n

/-- **The balancing number $B_2$ is $6$.** The balancing number $B_2$ equals $6$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem balancingNum_two : balancingNum 2 = 6 := rfl

/-- **The balancing number $B_3$ is $35$.** The balancing number $B_3$ equals $35$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem balancingNum_three : balancingNum 3 = 35 := rfl

/-- **Lucas-balancing numbers (shifted indexing).** The sequence of integers $(C_n)_{n \ge 0}$
defined by $C_0 = 3$, $C_1 = 1$ and $C_{n+2} = 6 C_{n+1} - C_n$ for all $n \ge 0$.

This is the indexing of Mohapatra, Bhoi and Panda, forced by the values $C_2 = 3$ and
$C_3 = 17$ displayed in their Theorem 3: for $n \ge 1$, $C_n$ is the usual Lucas-balancing
number $c_{n-1}$, where $c_0 = 1$, $c_1 = 3$ and $c_{n+2} = 6 c_{n+1} - c_n$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3. -/
public def lucasBalancingNum : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | n + 2 => 6 * lucasBalancingNum (n + 1) - lucasBalancingNum n

/-- **The Lucas-balancing number $C_2$ is $3$.** For the Lucas-balancing numbers defined by
$C_0 = 3$, $C_1 = 1$ and $C_{n+2} = 6C_{n+1} - C_n$, we have $C_2 = 3$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3. -/
public theorem lucasBalancingNum_two : lucasBalancingNum 2 = 3 := rfl

/-- **The Lucas-balancing number $C_3$ is $17$.** For the Lucas-balancing numbers defined by
$C_0 = 3$, $C_1 = 1$ and $C_{n+2} = 6C_{n+1} - C_n$, we have $C_3 = 17$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3. -/
public theorem lucasBalancingNum_three : lucasBalancingNum 3 = 17 := rfl

/-- **Decimal repdigits.** A natural number $n$ is a repdigit if there are natural numbers $d$
and $m$ with $1 \le d \le 9$ and $m \ge 1$ such that $9n = d(10^m - 1)$. Equivalently, $n$ is
the positive integer whose decimal expansion consists of $m$ copies of the digit $d$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Section 1 (definition of repdigit). -/
public def IsRepdigit (n : ℕ) : Prop :=
  ∃ d m : ℕ, 1 ≤ d ∧ d ≤ 9 ∧ 1 ≤ m ∧ 9 * n = d * (10 ^ m - 1)

/-- **Eleven is a repdigit.** The number $11$ is a repdigit.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem isRepdigit_eleven : IsRepdigit 11 :=
  ⟨1, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Nonzero single digits are repdigits.** Every natural number $d$ with $1 \le d \le 9$ is a
repdigit.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Section 1 (definition of repdigit). -/
public theorem isRepdigit_of_le (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ 9) :
    IsRepdigit d :=
  ⟨d, 1, h1, h2, le_rfl, by ring⟩

/-- **Concatenations of two decimal repdigits.** A natural number $n$ is a concatenation of two
repdigits if there are digits $d_1, d_2$ with $1 \le d_1 \le 9$, $0 \le d_2 \le 9$ and
$d_1 \ne d_2$, and block lengths $m_1, m_2 \ge 1$, such that the decimal expansion of $n$ is
$m_1$ copies of $d_1$ followed by $m_2$ copies of $d_2$; that is,
$9n = d_1 (10^{m_1} - 1) 10^{m_2} + d_2 (10^{m_2} - 1)$. Equivalently, the decimal expansion of
$n$ has exactly two runs of equal digits.

Because of the condition $d_1 \ne d_2$, a repdigit such as $99$ is not a concatenation of two
repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemmas 3 and 5. -/
public def IsConcatTwoRepdigits (n : ℕ) : Prop :=
  ∃ d₁ d₂ m₁ m₂ : ℕ, 1 ≤ d₁ ∧ d₁ ≤ 9 ∧ d₂ ≤ 9 ∧ 1 ≤ m₁ ∧ 1 ≤ m₂ ∧ d₁ ≠ d₂ ∧
    9 * n = d₁ * (10 ^ m₁ - 1) * 10 ^ m₂ + d₂ * (10 ^ m₂ - 1)

/-- **Concatenations of three decimal repdigits.** A natural number $n$ is a concatenation of
three repdigits if there are digits $d_1, d_2, d_3$ with $1 \le d_1 \le 9$, $0 \le d_2 \le 9$,
$0 \le d_3 \le 9$, $d_1 \ne d_2$ and $d_2 \ne d_3$, and block lengths $m_1, m_2, m_3 \ge 1$, such
that the decimal expansion of $n$ is $m_1$ copies of $d_1$, then $m_2$ copies of $d_2$, then $m_3$
copies of $d_3$; that is,
$$9n = d_1 (10^{m_1} - 1) 10^{m_2 + m_3} + d_2 (10^{m_2} - 1) 10^{m_3} + d_3 (10^{m_3} - 1).$$
Equivalently, the decimal expansion of $n$ has exactly three runs of equal digits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemmas 4 and 6. -/
public def IsConcatThreeRepdigits (n : ℕ) : Prop :=
  ∃ d₁ d₂ d₃ m₁ m₂ m₃ : ℕ, 1 ≤ d₁ ∧ d₁ ≤ 9 ∧ d₂ ≤ 9 ∧ d₃ ≤ 9 ∧
    1 ≤ m₁ ∧ 1 ≤ m₂ ∧ 1 ≤ m₃ ∧ d₁ ≠ d₂ ∧ d₂ ≠ d₃ ∧
    9 * n = d₁ * (10 ^ m₁ - 1) * 10 ^ (m₂ + m₃) + d₂ * (10 ^ m₂ - 1) * 10 ^ m₃ +
      d₃ * (10 ^ m₃ - 1)

/-- **$35$ is a concatenation of two repdigits.** The number $35$, whose decimal expansion consists
of the one-digit blocks $3$ and $5$, is a concatenation of two repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 3. -/
public theorem isConcatTwoRepdigits_thirtyFive : IsConcatTwoRepdigits 35 :=
  ⟨3, 5, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- **$204$ is a concatenation of three repdigits.** The number $204$, whose decimal expansion
consists of the one-digit blocks $2$, $0$ and $4$, is a concatenation of three repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 4. -/
public theorem isConcatThreeRepdigits_twoZeroFour : IsConcatThreeRepdigits 204 :=
  ⟨2, 0, 4, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Differences of two repdigits.** A natural number $n$ is a difference of two repdigits if
there are repdigits $a$ and $b$ with $a = n + b$, that is, $n = a - b$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorems 2 and 3. -/
public def IsRepdigitDiff (n : ℕ) : Prop :=
  ∃ a b : ℕ, IsRepdigit a ∧ IsRepdigit b ∧ a = n + b

/-- **Six is a difference of two repdigits.** The number $6$ is a difference of two repdigits:
$6 = 11 - 5$, where $11$ and $5$ are repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem isRepdigitDiff_six : IsRepdigitDiff 6 :=
  ⟨11, 5, isRepdigit_eleven, isRepdigit_of_le 5 (by norm_num) (by norm_num),
    rfl⟩

/-- **Balancing numbers that are concatenations of two repdigits.** For every natural number $k$,
if the balancing number $B_k$ is a concatenation of two repdigits, then $B_k = 35$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 3 (`integers-2025-A15-lem-3`). -/
public theorem_wanted balancingNum_concatTwoRepdigits (k : ℕ)
    (h : IsConcatTwoRepdigits (balancingNum k).toNat) :
    balancingNum k = 35

/-- **Balancing numbers that are concatenations of three repdigits.** For every natural number
$k$, if the balancing number $B_k$ is a concatenation of three repdigits, then $B_k = 204$ or
$B_k = 1189$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 4 (`integers-2025-A15-lem-4`). -/
public theorem_wanted balancingNum_concatThreeRepdigits (k : ℕ)
    (h : IsConcatThreeRepdigits (balancingNum k).toNat) :
    balancingNum k = 204 ∨ balancingNum k = 1189

/-- **Lucas-balancing numbers that are concatenations of two repdigits.** For every natural
number $k$, if the decimal expansion of the Lucas-balancing number $C_k$ consists of exactly two
runs of equal digits, that is, $C_k$ is a block of one repeated digit followed by a block of a
different repeated digit, then $C_k = 17$ or $C_k = 577$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 5 (`integers-2025-A15-lem-5`). -/
public theorem_wanted lucasBalancingNum_concatTwoRepdigits (k : ℕ)
    (h : IsConcatTwoRepdigits (lucasBalancingNum k).toNat) :
    lucasBalancingNum k = 17 ∨ lucasBalancingNum k = 577

/-- **Lucas-balancing numbers that are concatenations of three repdigits.** For every natural
number $k$, if the decimal expansion of the Lucas-balancing number $C_k$ consists of exactly
three runs of equal digits, that is, $C_k$ is three blocks of repeated digits in which adjacent
blocks have different digits, then $C_k = 3363$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 6 (`integers-2025-A15-lem-6`). -/
public theorem_wanted lucasBalancingNum_concatThreeRepdigits (k : ℕ)
    (h : IsConcatThreeRepdigits (lucasBalancingNum k).toNat) :
    lucasBalancingNum k = 3363

/-- **Balancing numbers that are differences of two repdigits.** Let $k \ge 2$ be a natural
number. If the balancing number $B_k$ is a difference of two repdigits, then $B_k = 6$ or
$B_k = 35$.

The hypothesis $k \ge 2$ excludes $B_0 = 0 = 1 - 1$ and $B_1 = 1 = 2 - 1$, which are also
differences of two repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2 (`integers-2025-A15-thm-2`). -/
public theorem_wanted balancingNum_repdigitDiff (k : ℕ) (hk : 2 ≤ k)
    (h : IsRepdigitDiff (balancingNum k).toNat) :
    balancingNum k = 6 ∨ balancingNum k = 35

/-- **Lucas-balancing numbers that are differences of two repdigits.** For every natural
number $k \ge 2$, if the Lucas-balancing number $C_k$ is a difference of two repdigits, then
$C_k = 3$ or $C_k = 17$.

Both values occur: $C_2 = 3 = 11 - 8$ and $C_3 = 17 = 22 - 5$. The hypothesis $k \ge 2$ excludes
$C_1 = 1 = 2 - 1$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3 (`integers-2025-A15-thm-3`). -/
public theorem_wanted lucasBalancingNum_repdigitDiff (k : ℕ) (hk : 2 ≤ k)
    (h : IsRepdigitDiff (lucasBalancingNum k).toNat) :
    lucasBalancingNum k = 3 ∨ lucasBalancingNum k = 17

end

end MetaMathlibExt
