/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Composition
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

/-- **Positional colored compositions.** For natural numbers $m$, $k$ and $\ell$, $c_{m,k}(\ell)$
is the number of $(m, k)$-colored compositions of $\ell$: compositions of $\ell$ in which every
part whose position, counted from $1$, is congruent to $k$ modulo $m$ gets one of $p$ colors,
where $p$ is the part, and the other parts are uncolored. Equivalently, $c_{m,k}(\ell)$ is the
sum, over all compositions $(p_1, \dots, p_r)$ of $\ell$, of the product of the parts $p_i$ with
$i \equiv k \pmod m$.

The paper takes $m \ge 1$. For $m = 0$, congruence modulo $0$ is equality, so only the part at
position exactly $k$ is colored.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Definition 1. -/
public def positionalColoredCompositionCount (m k ℓ : ℕ) : ℕ :=
  ∑ c : Composition ℓ, (c.blocks.mapIdx fun i p => if (i + 1) % m = k % m then p else 1).prod

/-- **Colored compositions of zero.** For all natural numbers $m$ and $k$, $c_{m,k}(0) = 1$: the
only composition of $0$ is the empty one.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Definition 1. -/
public theorem positionalColoredCompositionCount_zero (m k : ℕ) :
    positionalColoredCompositionCount m k 0 = 1 := by
  have h : (Finset.univ : Finset (Composition 0)) = {Composition.ones 0} := by decide
  simp [positionalColoredCompositionCount, h, Composition.ones]

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

/-- **Odd colored compositions and binomial-color compositions.** For every $k \ge 1$, the number
$o(k) = c_{2,1}(k)$ of odd colored compositions of $k$, in which only the parts at odd positions
are colored, equals the sum, over all compositions $(p_1, \dots, p_r)$ of $k + 1$, of
$\prod_i \binom{p_i}{2}$; that is, the number of compositions of $k + 1$ in which a part $p$ has
$\binom{p}{2}$ colors.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 2 (`integers-2026-A49-thm-2`). -/
public theorem_wanted odd_eq_choose_two_colorCompositions (k : ℕ) (hk : 1 ≤ k) :
    positionalColoredCompositionCount 2 1 k =
      ∑ c : Composition (k + 1), (c.blocks.map fun p => p.choose 2).prod

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

/-- **Even colored compositions and runs in binary strings.** For every $k \ge 0$, the number
$e(k + 1) = c_{2,0}(k + 1)$ of even colored compositions of $k + 1$, in which only the parts at
even positions are colored, equals the sum, over all binary strings of length $k$, of the
product of the lengths of the maximal runs of $1$s in the string; a string without a $1$
contributes the empty product $1$.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 4 (`integers-2026-A49-thm-4`). -/
public theorem_wanted even_succ_eq_sum_runLength_prod (k : ℕ) :
    positionalColoredCompositionCount 2 0 (k + 1) =
      ∑ f : Fin k → Bool,
        ((((List.ofFn f).splitOn false).map List.length).filter (· ≠ 0)).prod

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

/-- **A recurrence for positional colored compositions.** For natural numbers $m$, $k$ and $\ell$
with $m \ge 1$, $m \nmid k$ and $\ell \ge 1$,
$c_{m,k+1}(\ell + 1) = c_{m,k+1}(\ell) + c_{m,k}(\ell)$.

The paper prints the hypotheses $k \ge 1$, $\ell \ge 2$ and $1 \le m \le \ell - 1$, which allow
$m \mid k$; there the identity fails: for $m = 1$, $k = 1$ and $\ell = 2$ one has
$c_{1,2}(3) = 8$ but $c_{1,2}(2) + c_{1,1}(2) = 6$. The paper's argument (remove a first part
$1$ or decrease the first part) needs the first part to be uncolored, which is the condition
$m \nmid k$.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 6 (`integers-2026-A49-thm-6`). -/
public theorem_wanted positionalColoredCompositionCount_succ (m k ℓ : ℕ) (hm : 1 ≤ m)
    (hmk : ¬ m ∣ k) (hℓ : 1 ≤ ℓ) :
    positionalColoredCompositionCount m (k + 1) (ℓ + 1) =
      positionalColoredCompositionCount m (k + 1) ℓ + positionalColoredCompositionCount m k ℓ

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
