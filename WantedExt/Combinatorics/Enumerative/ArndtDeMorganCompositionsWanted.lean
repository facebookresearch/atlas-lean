/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Arndt and De Morgan compositions

Statements from Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*,
INTEGERS 26 (2026), Article A64.

The permutations `U` and `V` act on Mathlib's `Composition n`; the counts are over tuples of
positive integers, as in `kArndtCompositionCount`. The number `a(n, k)` of generalized Arndt
compositions of `n` (pairwise condition `c_{2i-1} > c_{2i} + k`) is `kArndtTotalCount k n`, the
sum over the number of parts of `kArndtCompositionCount k n m`
(`MathlibExt/Combinatorics/Enumerative/KArndtRecurrence.lean`).
`c^{2k}_o(n)` and `c^{2k+1}_e(n)` are `oddOrSmallEvenCompositionCount k n` and
`evenOrSmallOddCompositionCount k n`. The permutations `U` and `V` of the paper act on the list of
parts pair by pair; a final unpaired part `c` is the pair `(c, 0)` and maps to `c` parts `1`.
The map `arndtU`, its values and the theorem that it permutes compositions are in
`MathlibExt/Combinatorics/Enumerative/ArndtU.lean`; the same for `arndtV` is in
`MathlibExt/Combinatorics/Enumerative/ArndtV.lean`.
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.ArndtU
public import MathlibExt.Combinatorics.Enumerative.ArndtVFixed
public import MathlibExt.Combinatorics.Enumerative.ParityRestrictedCompositions
public import MathlibExt.Combinatorics.Enumerative.ArndtNegativeEven
public import MathlibExt.NumberTheory.PadovanSequence
public import WantedExt.Combinatorics.Enumerative.ArndtCompositionsGeneratingFunctionsWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Compositions of $5$ into even or small odd parts.** $c^1_e(5) = 10$ and $c^3_e(5) = 15$,
where $c^{2k+1}_e(n)$ is the number of compositions of $n$ in which every part is even or at
most $2k + 1$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 6 and the discussion after Theorem 6. -/
theorem evenOrSmallOddCompositionCount_five :
    evenOrSmallOddCompositionCount 0 5 = 10 ∧ evenOrSmallOddCompositionCount 1 5 = 15 := by
  decide

/-- **Arndt compositions and compositions into odd parts are equinumerous.** For every natural
number $n$, the number $a(n, 0)$ of Arndt compositions of $n$ (compositions $(c_1, \dots, c_m)$
of $n$ with $c_{2i-1} > c_{2i}$ whenever $2i \le m$) equals the number $c^0_o(n)$ of compositions
of $n$ into odd parts. This includes $n = 0$, where both counts are $1$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 1 (`integers-2026-A64-thm-1`). -/
public theorem_wanted kArndtTotalCount_zero_eq_odd_compositions (n : ℕ) :
    kArndtTotalCount 0 n = oddOrSmallEvenCompositionCount 0 n

/-- **Compositions fixed by $U$ and their Padovan count.** A composition $(c_1, \dots, c_m)$ of
$n$ is fixed by the map $U$ if and only if $c_i = 1$ for every odd $i$ and $c_i$ is even for
every even $i$. Let $c_U(n)$ be the number of compositions of $n$ fixed by $U$. Then
$c_U(n) = c_U(n - 2) + c_U(n - 3)$ for every $n \ge 4$, $c_U(1) = 1$, $c_U(2) = 0$,
$c_U(3) = 1$, and $c_U(n) = P_{n-1}$ for every $n \ge 1$, where $P$ is the shifted Padovan
sequence, given by $P_0 = 1$, $P_1 = 0$, $P_2 = 1$ and $P_{j+3} = P_{j+1} + P_j$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Proposition 1 (`integers-2026-A64-prop-1`). -/
public theorem_wanted arndtU_fixed_iff_and_count :
    (∀ (n : ℕ) (c : Composition n), arndtU c.blocks = c.blocks ↔
      ∀ (i : ℕ) (h : i < c.blocks.length),
        if i % 2 = 0 then c.blocks[i] = 1 else Even c.blocks[i]) ∧
    (∀ n : ℕ, 4 ≤ n →
      (Finset.univ.filter fun c : Composition n => arndtU c.blocks = c.blocks).card =
        (Finset.univ.filter fun c : Composition (n - 2) => arndtU c.blocks = c.blocks).card +
          (Finset.univ.filter fun c : Composition (n - 3) => arndtU c.blocks = c.blocks).card) ∧
    (Finset.univ.filter fun c : Composition 1 => arndtU c.blocks = c.blocks).card = 1 ∧
    (Finset.univ.filter fun c : Composition 2 => arndtU c.blocks = c.blocks).card = 0 ∧
    (Finset.univ.filter fun c : Composition 3 => arndtU c.blocks = c.blocks).card = 1 ∧
    ∀ n : ℕ, 1 ≤ n →
      (Finset.univ.filter fun c : Composition n => arndtU c.blocks = c.blocks).card =
        shiftedPadovanSequence (n - 1)

end

end MetaMathlibExt
