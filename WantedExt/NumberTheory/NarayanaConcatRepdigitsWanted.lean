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

/-- **Concatenations of two repdigits in a general base.** A natural number $n$ is a
concatenation of two repdigits in base $b$ if there are digits $a_1, a_2$ with
$1 \le a_1 \le b - 1$, $0 \le a_2 \le b - 1$ and $a_1 \ne a_2$, and block lengths $l, m \ge 1$,
such that $(b - 1) n = a_1 (b^l - 1) b^m + a_2 (b^m - 1)$. The digit conditions force
$b \ge 2$, and the equation says that the base-$b$ expansion of $n$ is $l$ copies of $a_1$
followed by $m$ copies of $a_2$.

Because of the condition $a_1 \ne a_2$, a repdigit such as $4 = (11)_3$ is not a concatenation
of two repdigits in base $3$. For $b = 10$ this is the notion of a concatenation of two decimal
repdigits.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Section 1 (Equation (1)). -/
public def IsConcatTwoRepdigitsBase (b n : ℕ) : Prop :=
  ∃ a₁ a₂ l m : ℕ, 1 ≤ a₁ ∧ a₁ < b ∧ a₂ < b ∧ 1 ≤ l ∧ 1 ≤ m ∧ a₁ ≠ a₂ ∧
    (b - 1) * n = a₁ * (b ^ l - 1) * b ^ m + a₂ * (b ^ m - 1)

/-- **Examples of two-repdigit concatenations in bases 2 and 5.** The number $4$ is a
concatenation of two repdigits in base $2$, since $4 = (100)_2$, and the number $406$ is a
concatenation of two repdigits in base $5$, since $406 = (3111)_5$.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Theorem 1. -/
public theorem isConcatTwoRepdigitsBase_examples :
    IsConcatTwoRepdigitsBase 2 4 ∧ IsConcatTwoRepdigitsBase 5 406 :=
  ⟨⟨1, 0, 1, 2, by norm_num⟩, ⟨3, 1, 1, 3, by norm_num⟩⟩

/-- **Narayana numbers that concatenate two repdigits in bases 2 to 9.** Let $(N_n)$ be
Narayana's cows sequence and let $2 \le b \le 9$. Then $N_n$ is a concatenation of two repdigits
in base $b$ if and only if $(n, b)$ is one of the following $43$ pairs: $n = 4$ and $b = 2$;
$n = 5$ and $b = 3$; $n = 6$ and $b \in \{2, 4\}$; $n = 7$ and $b \in \{2, 3, 4, 6\}$; $n = 8$
and $b \in \{3, 4, 5, 6, 7, 9\}$; $n = 9$ and $b \in \{4, 5, 6, 7, 8, 9\}$; $n = 10$ and
$b \in \{5, 6, 7, 8, 9\}$; $n = 11$ and $b \in \{2, 7, 8, 9\}$; $n = 12$ and
$b \in \{3, 4, 7, 8, 9\}$; $n = 13$ and $b \in \{2, 4, 5, 7, 8\}$; $n = 14$ and $b = 6$;
$n = 17$ and $b \in \{7, 9\}$; $n = 18$ and $b = 5$.

The corresponding values and expansions are $N_4 = 2 = (10)_2$, $N_5 = 3 = (10)_3$,
$N_6 = 4 = (100)_2 = (10)_4$, $N_7 = 6 = (110)_2 = (20)_3 = (12)_4 = (10)_6$,
$N_8 = 9 = (100)_3 = (21)_4 = (14)_5 = (13)_6 = (12)_7 = (10)_9$,
$N_9 = 13 = (31)_4 = (23)_5 = (21)_6 = (16)_7 = (15)_8 = (14)_9$,
$N_{10} = 19 = (34)_5 = (31)_6 = (25)_7 = (23)_8 = (21)_9$,
$N_{11} = 28 = (11100)_2 = (40)_7 = (34)_8 = (31)_9$,
$N_{12} = 41 = (1112)_3 = (221)_4 = (56)_7 = (51)_8 = (45)_9$,
$N_{13} = 60 = (111100)_2 = (330)_4 = (220)_5 = (114)_7 = (74)_8$, $N_{14} = 88 = (224)_6$,
$N_{17} = 277 = (544)_7 = (337)_9$ and $N_{18} = 406 = (3111)_5$.

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

/-- **Logarithmic bounds for Narayana numbers that concatenate two repdigits.** Let $(N_n)$ be
Narayana's cows sequence and let $\alpha$ be a real number with $\alpha^3 = \alpha^2 + 1$ (so
$\alpha \approx 1.46557$ is the unique real root of $x^3 - x^2 - 1$). Let $b \ge 2$, $n \ge 1$
and $l, m \ge 1$ be natural numbers, and let $a_1, a_2$ be digits with $1 \le a_1 \le b - 1$,
$0 \le a_2 \le b - 1$ and $a_1 \ne a_2$. If $(b - 1) N_n = a_1 (b^l - 1) b^m + a_2 (b^m - 1)$,
that is, the base-$b$ expansion of $N_n$ is $l$ copies of $a_1$ followed by $m$ copies of
$a_2$, then $(l + m - 1) \log b + \log \alpha < n \log \alpha < (l + m) \log b + 1$.

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
