/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Narayana numbers that are concatenations of two base-`b` repdigits

Statements from Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations
of Two Base b Repdigits*, INTEGERS 24 (2024), Article A20.

Narayana's cows sequence is `MetaMathlibExt.narayanaCowsSequence` (`N₀ = 0`, `N₁ = N₂ = 1`,
`Nₙ = Nₙ₋₁ + Nₙ₋₃`), whose indexing matches the paper (`N₄ = 2`, `N₁₈ = 406`).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Insert
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence

namespace MetaMathlibExt

@[expose] public section

/-- `n` is a concatenation of two repdigits in base `b`: its base-`b` expansion is a block of
`l ≥ 1` copies of a digit `a₁ ∈ [1, b - 1]` followed by a block of `m ≥ 1` copies of a digit
`a₂ ∈ [0, b - 1]` with `a₁ ≠ a₂`, i.e.
`(b - 1) n = a₁ (b^l - 1) b^m + a₂ (b^m - 1)` (the paper's Equation (1)). Distinctness is
required by the paper's list: repdigits such as `4 = (11)₃` are not counted. For `b = 10`
this is `IsConcatTwoRepdigits`.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Section 1 (Equation (1)). -/
public def IsConcatTwoRepdigitsBase (b n : ℕ) : Prop :=
  ∃ a₁ a₂ l m : ℕ, 1 ≤ a₁ ∧ a₁ < b ∧ a₂ < b ∧ 1 ≤ l ∧ 1 ≤ m ∧ a₁ ≠ a₂ ∧
    (b - 1) * n = a₁ * (b ^ l - 1) * b ^ m + a₂ * (b ^ m - 1)

/-- `4 = (100)₂` and `406 = (3111)₅` are concatenations of two repdigits.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Theorem 1. -/
public theorem isConcatTwoRepdigitsBase_examples :
    IsConcatTwoRepdigitsBase 2 4 ∧ IsConcatTwoRepdigitsBase 5 406 :=
  ⟨⟨1, 0, 1, 2, by norm_num⟩, ⟨3, 1, 1, 3, by norm_num⟩⟩

/-- Theorem 1: for `2 ≤ b ≤ 9`, `Nₙ` is a concatenation of two base-`b` repdigits exactly for
the pairs `(n, b)` of the paper's list: the values are `2, 3, 4, 6, 9, 13, 19, 28, 41, 60, 88,
277, 406` (`n = 4, …, 14, 17, 18`), with `2 = (10)₂`, `3 = (10)₃`, `4 = (100)₂ = (10)₄`,
`6 = (110)₂ = (20)₃ = (12)₄ = (10)₆`, `9 = (100)₃ = (21)₄ = (14)₅ = (13)₆ = (12)₇ = (10)₉`,
`13 = (31)₄ = (23)₅ = (21)₆ = (16)₇ = (15)₈ = (14)₉`, `19 = (34)₅ = (31)₆ = (25)₇ = (23)₈ =
(21)₉`, `28 = (11100)₂ = (40)₇ = (34)₈ = (31)₉`, `41 = (1112)₃ = (221)₄ = (56)₇ = (51)₈ =
(45)₉`, `60 = (111100)₂ = (330)₄ = (220)₅ = (114)₇ = (74)₈`, `88 = (224)₆`,
`277 = (544)₇ = (337)₉`, `406 = (3111)₅`.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Theorem 1 (`integers-2024-A20-thm-1`). -/
public theorem_wanted narayanaCowsSequence_isConcatTwoRepdigitsBase_iff {n b : ℕ} (hb : 2 ≤ b)
    (hb9 : b ≤ 9) :
    IsConcatTwoRepdigitsBase b (narayanaCowsSequence n) ↔
      (n, b) ∈ ({(4, 2), (5, 3), (6, 2), (6, 4), (7, 2), (7, 3), (7, 4), (7, 6), (8, 3),
        (8, 4), (8, 5), (8, 6), (8, 7), (8, 9), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9),
        (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, 2), (11, 7), (11, 8), (11, 9),
        (12, 3), (12, 4), (12, 7), (12, 8), (12, 9), (13, 2), (13, 4), (13, 5), (13, 7),
        (13, 8), (14, 6), (17, 7), (17, 9), (18, 5)} : Finset (ℕ × ℕ))

/-- Lemma 3 (Guzmán Sánchez and Luca): for real `r ≥ 1` and `H` with `H > (4r²)^r` and
`H > L / (log L)^r`, we have `L < 2^r H (log H)^r`. The hypothesis `H > 0` is implied by
`H > (4r²)^r` and is dropped.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Lemma 3 (`integers-2024-A20-lem-3`). -/
public theorem_wanted lt_two_rpow_mul_mul_log_rpow {r H L : ℝ} (hr : 1 ≤ r)
    (hH : (4 * r ^ 2) ^ r < H) (hL : L / Real.log L ^ r < H) :
    L < 2 ^ r * H * Real.log H ^ r

/-- Lemma 1: every solution of Equation (1), `Nₙ = a₁…a₁a₂…a₂` in base `b ≥ 2` with `l ≥ 1`
copies of `a₁ ∈ [1, b - 1]`, `m ≥ 1` copies of `a₂ ∈ [0, b - 1]`, `a₁ ≠ a₂` and `n ≥ 1`,
satisfies `(l + m - 1) log b + log α < n log α < (l + m) log b + 1`, where `α ≈ 1.46557` is the
real root of `x³ - x² - 1` (its only real root).

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Lemma 1 (`integers-2024-A20-lem-1`). -/
public theorem_wanted narayanaCowsSequence_concat_log_bounds {α : ℝ} (hα : α ^ 3 = α ^ 2 + 1)
    {n b a₁ a₂ l m : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (ha₁ : 1 ≤ a₁) (ha₁b : a₁ < b)
    (ha₂b : a₂ < b) (hl : 1 ≤ l) (hm : 1 ≤ m) (hne : a₁ ≠ a₂)
    (heq : (b - 1) * narayanaCowsSequence n = a₁ * (b ^ l - 1) * b ^ m + a₂ * (b ^ m - 1)) :
    ((l + m - 1 : ℕ) : ℝ) * Real.log b + Real.log α < n * Real.log α ∧
      n * Real.log α < ((l + m : ℕ) : ℝ) * Real.log b + 1

end

end MetaMathlibExt
