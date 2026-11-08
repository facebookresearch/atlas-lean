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

/-- The balancing numbers `B_n`, defined by `B_0 = 0`, `B_1 = 1` and
`B_{n+2} = 6 B_{n+1} - B_n`.

Source: standard definition used in "Balancing and Lucas-Balancing Numbers as
the Difference of Two Repdigits" (Integers 2025, A15); the values
`B_2 = 6`, `B_3 = 35` are those displayed in its Theorem 2. -/
public def balancingNum : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 6 * balancingNum (n + 1) - balancingNum n

/-- Characteristic value `B_2 = 6`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem balancingNum_two : balancingNum 2 = 6 := rfl

/-- Characteristic value `B_3 = 35`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem balancingNum_three : balancingNum 3 = 35 := rfl

/-- The Lucas-balancing numbers in the indexing of Integers 2025, A15, defined
by `C_0 = 3`, `C_1 = 1` and `C_{n+2} = 6 C_{n+1} - C_n`.

This indexing is forced by the values displayed in the paper's Theorem 3,
`C_2 = 3` and `C_3 = 17` (thus the paper's `C_n` for `n ≥ 1` is the usual
Lucas-balancing number `c_{n-1}` with `c_0 = 1`, `c_1 = 3`).

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3. -/
public def lucasBalancingNum : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | n + 2 => 6 * lucasBalancingNum (n + 1) - lucasBalancingNum n

/-- Characteristic value `C_2 = 3`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3. -/
public theorem lucasBalancingNum_two : lucasBalancingNum 2 = 3 := rfl

/-- Characteristic value `C_3 = 17`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3. -/
public theorem lucasBalancingNum_three : lucasBalancingNum 3 = 17 := rfl

/-- A (decimal) repdigit: a positive integer all of whose decimal digits are
equal to some `d` with `1 ≤ d ≤ 9`, with `m ≥ 1` digits.

The condition is written without division as `9 * n = d * (10^m - 1)`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Section 1 (definition of repdigit). -/
public def IsRepdigit (n : ℕ) : Prop :=
  ∃ d m : ℕ, 1 ≤ d ∧ d ≤ 9 ∧ 1 ≤ m ∧ 9 * n = d * (10 ^ m - 1)

/-- Characteristic example: `11` is a repdigit.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem isRepdigit_eleven : IsRepdigit 11 :=
  ⟨1, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Characteristic example: every nonzero single digit is a repdigit.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Section 1 (definition of repdigit). -/
public theorem isRepdigit_of_le (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ 9) :
    IsRepdigit d :=
  ⟨d, 1, h1, h2, le_rfl, by ring⟩

/-- Concatenation of two repdigits (in the strict sense of Integers 2025,
A15): the decimal expansion of `n` consists of a block of `m₁ ≥ 1` digits
`d₁ ∈ [1, 9]` followed by a block of `m₂ ≥ 1` digits `d₂ ∈ [0, 9]` with
`d₁ ≠ d₂`, i.e. the expansion has exactly two digit runs.

The distinctness condition is required by the paper's classifications: for
example `C_4 = 99` is not listed in its Lemma 5.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemmas 3 and 5. -/
public def IsConcatTwoRepdigits (n : ℕ) : Prop :=
  ∃ d₁ d₂ m₁ m₂ : ℕ, 1 ≤ d₁ ∧ d₁ ≤ 9 ∧ d₂ ≤ 9 ∧ 1 ≤ m₁ ∧ 1 ≤ m₂ ∧ d₁ ≠ d₂ ∧
    9 * n = d₁ * (10 ^ m₁ - 1) * 10 ^ m₂ + d₂ * (10 ^ m₂ - 1)

/-- Concatenation of three repdigits: the decimal expansion has exactly three
digit runs, of digits `d₁ ∈ [1, 9]`, `d₂, d₃ ∈ [0, 9]` with `d₁ ≠ d₂` and
`d₂ ≠ d₃`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemmas 4 and 6. -/
public def IsConcatThreeRepdigits (n : ℕ) : Prop :=
  ∃ d₁ d₂ d₃ m₁ m₂ m₃ : ℕ, 1 ≤ d₁ ∧ d₁ ≤ 9 ∧ d₂ ≤ 9 ∧ d₃ ≤ 9 ∧
    1 ≤ m₁ ∧ 1 ≤ m₂ ∧ 1 ≤ m₃ ∧ d₁ ≠ d₂ ∧ d₂ ≠ d₃ ∧
    9 * n = d₁ * (10 ^ m₁ - 1) * 10 ^ (m₂ + m₃) + d₂ * (10 ^ m₂ - 1) * 10 ^ m₃ +
      d₃ * (10 ^ m₃ - 1)

/-- Characteristic example: `35 = "3" ‖ "5"` is a concatenation of two
repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 3. -/
public theorem isConcatTwoRepdigits_thirtyFive : IsConcatTwoRepdigits 35 :=
  ⟨3, 5, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- Characteristic example: `204 = "2" ‖ "0" ‖ "4"` is a concatenation of three
repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 4. -/
public theorem isConcatThreeRepdigits_twoZeroFour : IsConcatThreeRepdigits 204 :=
  ⟨2, 0, 4, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Expressible as a difference of two repdigits: `n = a - b` with `a, b`
repdigits and `a ≥ n`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorems 2 and 3. -/
public def IsRepdigitDiff (n : ℕ) : Prop :=
  ∃ a b : ℕ, IsRepdigit a ∧ IsRepdigit b ∧ a = n + b

/-- Characteristic example: `6 = 11 - 5` is a difference of two repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem isRepdigitDiff_six : IsRepdigitDiff 6 :=
  ⟨11, 5, isRepdigit_eleven, isRepdigit_of_le 5 (by norm_num) (by norm_num),
    rfl⟩

/-- The only balancing number that is a concatenation of two repdigits is `35`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 3 (`integers-2025-A15-lem-3`). -/
public theorem_wanted balancingNum_concatTwoRepdigits (k : ℕ)
    (h : IsConcatTwoRepdigits (balancingNum k).toNat) :
    balancingNum k = 35

/-- The only balancing numbers that are concatenations of three repdigits are `204` and `1189`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 4 (`integers-2025-A15-lem-4`). -/
public theorem_wanted balancingNum_concatThreeRepdigits (k : ℕ)
    (h : IsConcatThreeRepdigits (balancingNum k).toNat) :
    balancingNum k = 204 ∨ balancingNum k = 1189

/-- The only Lucas-balancing numbers that are concatenations of two repdigits are `17` and `577`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 5 (`integers-2025-A15-lem-5`). -/
public theorem_wanted lucasBalancingNum_concatTwoRepdigits (k : ℕ)
    (h : IsConcatTwoRepdigits (lucasBalancingNum k).toNat) :
    lucasBalancingNum k = 17 ∨ lucasBalancingNum k = 577

/-- The only Lucas-balancing number that is a concatenation of three repdigits is `3363`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 6 (`integers-2025-A15-lem-6`). -/
public theorem_wanted lucasBalancingNum_concatThreeRepdigits (k : ℕ)
    (h : IsConcatThreeRepdigits (lucasBalancingNum k).toNat) :
    lucasBalancingNum k = 3363

/-- If `B_k` is a difference of two repdigits then `B_k ∈ {6, 35}`; the paper displays
`B_2 = 6 = 11 - 5` and `B_3 = 35 = 44 - 9`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2 (`integers-2025-A15-thm-2`).

The hypothesis `2 ≤ k` is included because `B_1 = 1 = 2 - 1` is also a
difference of two repdigits but is not in the paper's list; with `k ≥ 2` the
statement was verified computationally for `k ≤ 9`. -/
public theorem_wanted balancingNum_repdigitDiff (k : ℕ) (hk : 2 ≤ k)
    (h : IsRepdigitDiff (balancingNum k).toNat) :
    balancingNum k = 6 ∨ balancingNum k = 35

/-- If `C_k` is a difference of two repdigits then `C_k ∈ {3, 17}`; the paper displays
`C_2 = 3 = 11 - 8` and `C_3 = 17 = 22 - 5`.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3 (`integers-2025-A15-thm-3`).

The hypothesis `2 ≤ k` excludes `C_1 = 1 = 2 - 1`, as in Theorem 2. -/
public theorem_wanted lucasBalancingNum_repdigitDiff (k : ℕ) (hk : 2 ≤ k)
    (h : IsRepdigitDiff (lucasBalancingNum k).toNat) :
    lucasBalancingNum k = 3 ∨ lucasBalancingNum k = 17

end

end MetaMathlibExt
