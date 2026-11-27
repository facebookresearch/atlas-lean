/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.MultiplicativeAdditiveEightSquares
public import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquares
public import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresRigidity
public import MathlibExt.NumberTheory.MultiplicativeAdditiveThreePairedSquares
public import MathlibExt.NumberTheory.SixAndEightNonzeroSquares
public import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresEqIdOfThreeOrFour
public import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresDichotomy
public import MathlibExt.NumberTheory.MultiplicativeAdditiveSixSquares

namespace MetaMathlibExt

@[expose] public section

/-! # Multiplicative functions additive on partitions of `2k` nonzero squares

Statements from Mahajan's paper. Equation (1) of the paper is
`f(∑_{i=1}^{2k} x_i²) = ∑_{j=1}^{k} f(x_{2j-1}² + x_{2j}²)` for all positive integers
`x_1, …, x_{2k}`; it is written here with the pairs `(x_{2j-1}, x_{2j})` relabelled as
`(x j, y j)` for `j : Fin k`. Equation (2) is `k`-additivity on
`E₂ = {a² + b² : a, b ≥ 1}`. A multiplicative function `ℕ → ℂ` is an
`ArithmeticFunction ℂ` with `IsMultiplicative`; its value at `0` plays no role.
-/

open ArithmeticFunction

/-- **Dubouis's theorem on sums of nonzero squares.** Let $m \ge 4$ and let $n$ be a positive
integer. Then $n$ is a sum of $m$ squares of positive integers if and only if $n$ does not lie in
the exceptional set $E_m$, where
$E_4 = \{1, 3, 5, 9, 11, 17, 29, 41\} \cup \{2 \cdot 4^r, 6 \cdot 4^r, 14 \cdot 4^r : r \ge 0\}$,
$E_5 = \{1, 2, 3, 4, 6, 7, 9, 10, 12, 15, 18, 33\}$, and for $m \ge 6$,
$E_m = \{1, \dots, m - 1\} \cup \{m + 1, m + 2, m + 4, m + 5, m + 7, m + 10, m + 13\}$.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Lemma 1 (`integers-2026-A121-lem-1`), quoting
Dubouis (1911). -/
public theorem_wanted sum_nonzero_squares_iff_not_mem_exceptional (m n : ℕ) (hm : 4 ≤ m)
    (hn : 0 < n) :
    (∃ a : Fin m → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n) ↔
      n ∉ (if m = 4 then
            ({1, 3, 5, 9, 11, 17, 29, 41} : Set ℕ) ∪
              {n | ∃ r : ℕ, n = 2 * 4 ^ r ∨ n = 6 * 4 ^ r ∨ n = 14 * 4 ^ r}
          else if m = 5 then ({1, 2, 3, 4, 6, 7, 9, 10, 12, 15, 18, 33} : Set ℕ)
          else Set.Ico 1 m ∪
            {m + 1, m + 2, m + 4, m + 5, m + 7, m + 10, m + 13})

end

end MetaMathlibExt
