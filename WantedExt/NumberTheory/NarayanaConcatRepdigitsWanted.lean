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
public import Mathlib.Data.Finset.Insert
public import MathlibExt.Analysis.SpecialFunctions.Log.GuzmanSanchezLuca
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.NarayanaConcatRepdigits

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
