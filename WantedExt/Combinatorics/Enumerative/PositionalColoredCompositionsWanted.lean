/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.PositionalColoredCompositionChooseTwo
public import MathlibExt.Combinatorics.Enumerative.PositionalColoredCompositionRuns
public import Mathlib.Data.Set.Card

/-!
# Positional colored compositions (statements)

Statement-only targets from Andrew Li and Hua Wang, *Combinatorics of Positional Colored
Compositions*, INTEGERS 26 (2026), Article A49. In an `(m, k)`-`n`-colored composition the
parts at positions `≡ k (mod m)` (positions counted from `1`) carry a color from `1` to the part,
the other parts are uncolored; `c_{m,k}(ℓ)` is `positionalColoredCompositionCount m k ℓ`. EVEN
colored compositions are the case `(2, 0)` (count `e(ℓ)`) and ODD colored compositions the
case `(2, 1)` (count `o(ℓ)`). Ternary and binary strings are lists over `Fin 3` and `Bool`; a
string avoids `01` and `12` when neither occurs as a contiguous factor (`List.IsInfix`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Avoiding color 2 counts even colored compositions.** For every $k \ge 0$, the number of
$n$-color compositions of $k$ that do not use the color $2$ equals the number
$e(k) = c_{2,0}(k)$ of even colored compositions of $k$, in which only the parts at even
positions are colored. In such an $n$-color composition a part $p \ge 2$ has the $p - 1$ colors
other than $2$ and a part $1$ has its single color, so their number is the sum, over all
compositions $(p_1, \dots, p_r)$ of $k$, of $\prod_i q(p_i)$, where $q(1) = 1$ and
$q(p) = p - 1$ for $p \ge 2$.

The paper states this for positive $k$; at $k = 0$ both sides equal $1$.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 1 (`integers-2026-A49-thm-1`). -/
public theorem_wanted colorTwoRestrictedCompositions_eq_even (k : ℕ) :
    ∑ c : Composition k, (c.blocks.map fun p => if 2 ≤ p then p - 1 else p).prod =
      positionalColoredCompositionCount 2 0 k

/-- **Odd colored compositions and ternary strings.** For every $k \ge 1$, the number
$o(k) = c_{2,1}(k)$ of odd colored compositions of $k$, in which only the parts at odd positions
are colored, equals the number of strings of length $k - 1$ over the alphabet $\{0, 1, 2\}$ that
contain neither $01$ nor $12$ as two consecutive letters.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Corollary 1 (`integers-2026-A49-cor-1`). -/
public theorem_wanted odd_eq_ternaryStrings_avoiding (k : ℕ) (hk : 1 ≤ k) :
    positionalColoredCompositionCount 2 1 k =
      {w : List (Fin 3) | w.length = k - 1 ∧ ¬ [0, 1] <:+: w ∧ ¬ [1, 2] <:+: w}.ncard

/-- **Even colored compositions and ternary strings.** For every $k \ge 0$, the number
$e(k) = c_{2,0}(k)$ of even colored compositions of $k$, in which only the parts at even
positions are colored, equals the number of strings of length $k$ over the alphabet
$\{0, 1, 2\}$ that contain neither $01$ nor $12$ as two consecutive letters, do not begin with
$2$ and do not end with $0$.

At $k = 0$ both sides equal $1$, the empty string being counted.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 3 (`integers-2026-A49-thm-3`). -/
public theorem_wanted even_eq_ternaryStrings_avoiding (k : ℕ) :
    positionalColoredCompositionCount 2 0 k =
      {w : List (Fin 3) | w.length = k ∧ ¬ [0, 1] <:+: w ∧ ¬ [1, 2] <:+: w ∧
        w.head? ≠ some 2 ∧ w.getLast? ≠ some 0}.ncard

/-- **Odd colored compositions and runs in binary strings.** For every $k \ge 1$, the number
$o(k) = c_{2,1}(k)$ of odd colored compositions of $k$, in which only the parts at odd positions
are colored, equals the sum, over the binary strings of length $k$ whose first letter is $1$, of
the product of the lengths of the maximal runs of $1$s in the string.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 5 (`integers-2026-A49-thm-5`). -/
public theorem_wanted odd_eq_sum_runLength_prod (k : ℕ) (hk : 1 ≤ k) :
    positionalColoredCompositionCount 2 1 k =
      ∑ f ∈ (Finset.univ : Finset (Fin k → Bool)).filter (fun f => (List.ofFn f).head? = some true),
        ((((List.ofFn f).splitOn false).map List.length).filter (· ≠ 0)).prod

/-- **Even colored compositions and 321-avoiding separable permutations.** For every $k \ge 0$,
the number $e(k) = c_{2,0}(k)$ of even colored compositions of $k$, in which only the parts at
even positions are colored, equals the number of permutations of $\{1, \dots, k\}$ that avoid
the patterns $321$, $2413$ and $3142$, that is, the number of $321$-avoiding separable
permutations of $\{1, \dots, k\}$.

At $k = 0$ both sides equal $1$.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 7 (`integers-2026-A49-thm-7`). -/
public theorem_wanted even_eq_card_separable_321_avoiding (k : ℕ) :
    positionalColoredCompositionCount 2 0 k =
      Nat.card {σ : Equiv.Perm (Fin k) //
        (¬ ∃ a b c : Fin k, a < b ∧ b < c ∧ σ c < σ b ∧ σ b < σ a) ∧
        (¬ ∃ a b c d : Fin k, a < b ∧ b < c ∧ c < d ∧ σ c < σ a ∧ σ a < σ d ∧ σ d < σ b) ∧
        (¬ ∃ a b c d : Fin k, a < b ∧ b < c ∧ c < d ∧ σ b < σ d ∧ σ d < σ a ∧ σ a < σ c)}

end

end MetaMathlibExt
