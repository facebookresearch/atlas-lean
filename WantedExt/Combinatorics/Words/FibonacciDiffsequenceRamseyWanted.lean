/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.Combinatorics.EvenFibonacciAccessibility
public import MathlibExt.Combinatorics.HalfEvenFibonacciSet
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWordBeatty
public import MathlibExt.NumberTheory.FibonacciDivGoldenRatio
public import MathlibExt.NumberTheory.FractGoldenRatioDifferences
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.WesleyFractionalConstant
public import WantedExt.Combinatorics.AccessibleSetsWanted

/-!
# Ramsey-type theorems for Fibonacci numbers (statements)

Statement-only targets from William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci
Numbers and Other Sequences*, INTEGERS 25 (2025), Article A29.

Diffsequences, `r`-accessibility (`IsRAccessible`), `D`-progressions (`IsDAP`) and
`r`-largeness (`IsRLarge`, the paper's `r`-regularity of `AP_D`) are reused from
`WantedExt.Combinatorics.AccessibleSetsWanted`, as are the sets `positiveFibonacciSet` (`F`) and
`evenFibonacciSet` (`F_E`). `doa(D) ≤ r - 1` is stated as "not `s`-accessible for every `s ≥ r`",
and `Δ(D, k; r) = ∞` as the existence of an `r`-coloring of `ℤ⁺` with no monochromatic `k`-term
`D`-diffsequence (the form the proofs construct; equivalent to the finite version by
compactness).

The infinite Fibonacci word `F∞ = 010010100…` is MathlibExt's `fibInf` (zero-based, `false`
for the letter `0`); the paper indexes words from `1`, so the paper's `F∞(n)` is `fibInf (n - 1)`.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped Pointwise

/-- **The first ten letters of Wesley's words $S$ and $T$.** Indexing letters from $0$, the
letters of $S$ at indices $0, 1, \dots, 9$ are $1, 0, 0, 1, 1, 0, 1, 0, 0, 1$ and the letters of
$T$ at indices $0, 1, \dots, 9$ are $1, 0, 0, 1, 1, 0, 0, 1, 0, 0$; that is, $S$ begins with
$1001101001$ and $T$ begins with $1001100100$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Definition 1. -/
theorem wesleyWords_first_ten :
    (List.range 10).map wesleyWordS =
        [true, false, false, true, true, false, true, false, false, true] ∧
      (List.range 10).map wesleyWordT =
        [true, false, false, true, true, false, false, true, false, false] := by
  decide

/-! ## Statements -/

/-- **Arithmetic progressions with Fibonacci gaps are not $2$-regular.** There is a coloring of the
positive integers with two colors that admits no monochromatic $5$-term arithmetic progression
with gap in the positive Fibonacci set $\{1, 2, 3, 5, 8, \dots\}$, that is, no positive integers
$x_0, \dots, x_4$ of one color with $x_i = a + i d$ for all $i < 5$, for a positive integer $a$ and
a positive Fibonacci number $d$. Moreover, the positive Fibonacci set is $1$-large, and it is not
$r$-large for any natural number $r \ge 2$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Theorem 2 (`integers-2025-A29-thm-2`). -/
public theorem_wanted fibonacci_gap_progressions_not_two_regular :
    (∃ c : ℕ+ → Fin 2, ¬ ∃ x : Fin 5 → ℕ+,
      IsMonochromatic c x ∧ IsDAP positiveFibonacciSet 5 x) ∧
    IsRLarge 1 positiveFibonacciSet ∧ ∀ r, 2 ≤ r → ¬ IsRLarge r positiveFibonacciSet

/-- **The Lucas numbers are not $4$-accessible.** Let $L = \{2, 1, 3, 4, 7, \dots\}$ be the set of
Lucas numbers $L_0 = 2$, $L_1 = 1$, $L_{n+2} = L_{n+1} + L_n$. There is a coloring of the positive
integers with the colors $0, 1, 2, 3$ for which no sequence $x_0, x_1, x_2$ of positive integers is
both monochromatic and an $L$-diffsequence; and $L$ is not $r$-accessible for any $r \ge 4$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 6 (`integers-2025-A29-lem-6`). -/
public theorem_wanted lucasSet_not_four_accessible :
    (∃ c : ℕ+ → Fin 4, ¬ ∃ x : Fin 3 → ℕ+,
      IsMonochromatic c x ∧ IsDDiffSequence (Set.range lucasNumber) (fun i => ((x i : ℕ) : ℤ))) ∧
    ∀ r, 4 ≤ r → ¬ IsRAccessible r (Set.range lucasNumber)

end

end MetaMathlibExt
