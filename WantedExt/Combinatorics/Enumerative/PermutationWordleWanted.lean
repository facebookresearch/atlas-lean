/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.PermutationWordleCounts
public import MathlibExt.Combinatorics.Enumerative.PermutationWordleDerangements
public import MathlibExt.Combinatorics.Enumerative.PermutationWordleFirstCorrectThree
public import MathlibExt.Combinatorics.Enumerative.PermutationWordleFirstCorrectTwo
public import MathlibExt.Combinatorics.Enumerative.PermutationWordleLeftShift
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Permutation Wordle

Statements from Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer
Sequences 29 (2026), Article 26.1.7 (arXiv:2506.23452).

A guesser tries to find a secret permutation `π` of `Fin n`. The first guess is the identity;
after each guess the set of incorrect positions `I` is revealed, the correct positions are
locked, and the next guess permutes the entries on `I` by the strategy component `S |I|`: with
`I = {i₀ < i₁ < ⋯ < i_{m-1}}`, the entry at `i_j` moves to `i_{S m j}`. Positions are zero-based,
so the paper's one-line component `[2, 3, …, m, 1]` (cyclic shift) is `finRotate m`, and the
paper's guess `γ_{r+1}` is `permWordleGuess S π r`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Cyclic shift maximizes three-guess solves among inductive strategies.** Let $n \ge 4$ and let
$S$ be an inductive strategy of length $n$ whose component $S[n]$ is not the rotation
$i \mapsto i + 1 \pmod n$. Then strictly fewer permutations of $\{0, \dots, n-1\}$ are guessed in
exactly three guesses with $S$ than with the cyclic shift strategy.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 7 (`jis-2026-26.1.7-thm-7`). -/
public theorem_wanted permWordleCoeff_three_lt_cyclicShift (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ finRotate n) :
    permWordleCoeff S n 3 < permWordleCoeff cyclicShiftStrategy n 3

/-- **Three-guess solves of permutations with a fixed point.** Let $n \ge 4$ and let $S$ be a
permutation Wordle strategy (a permutation $S[m]$ of $\{0, \dots, m-1\}$ for each $m$) with
$S[m]$ equal to the cyclic shift $j \mapsto j + 1 \bmod m$ for every $m < n$. The number of
permutations $\pi$ of $\{0, \dots, n-1\}$ that $S$ guesses in exactly three guesses and whose
first guess (the identity) has a correct position, that is, $\pi$ has a fixed point, is
$1 - 2^{n+1} + 3^n + n^2/2 + 5n/2 - n \cdot 2^n$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 10 (`jis-2026-26.1.7-thm-10`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_one (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : ∀ m < n, S m = finRotate m) :
    (Nat.card {π : Equiv.Perm (Fin n) //
        PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 1} : ℚ) =
      1 - 2 ^ (n + 1) + 3 ^ n + (n : ℚ) ^ 2 / 2 + 5 * (n : ℚ) / 2 - n * 2 ^ n

/-- **Upper bound on three-guess solves first correct at guess two.** Let $n \ge 4$ and let $S$
be an inductive strategy of length $n$ whose component $S[n]$ is not the cyclic shift
$j \mapsto j + 1 \bmod n$ of $\{0, \dots, n-1\}$. Then fewer than $2^n - 2n - 2$ permutations
$\pi$ of $\{0, \dots, n-1\}$ are guessed by $S$ in exactly three guesses with the second guess
being the first guess that has a correct position.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 13 (`jis-2026-26.1.7-thm-13`). -/
public theorem_wanted card_solvedIn_three_firstCorrectAt_two_lt (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ finRotate n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 2} < 2 ^ n - 2 * n - 2

/-- **Cyclic shift left minimizes three-guess solves among inductive strategies.** Let $n \ge 4$
and let $S$ be an inductive strategy of length $n$ whose component $S[n]$ is not the left cyclic
shift $i \mapsto i - 1 \pmod n$. Then strictly fewer permutations of $\{0, \dots, n-1\}$ are
guessed in exactly three guesses with the cyclic shift left strategy $\mathrm{CSL}_n$ than with
$S$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 14 (`jis-2026-26.1.7-thm-14`). -/
public theorem_wanted permWordleCoeff_three_cyclicShiftLeft_lt (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ (finRotate n).symm) :
    permWordleCoeff (cyclicShiftLeftStrategy n) n 3 < permWordleCoeff S n 3

/-- **Among inductive strategies, cyclic shift left minimizes three-guess solves first correct at
guess two.** Let $n \ge 4$ and let $S$ be an inductive strategy of length $n$ whose component
$S[n]$ is not the left cyclic shift $i \mapsto i - 1 \pmod n$ of $\{0, \dots, n-1\}$. Let
$\mathrm{CSL}_n$ be the cyclic shift left strategy, whose component on $n$ positions is the left
cyclic shift and whose component on $m \ne n$ positions is the rotation $i \mapsto i + 1 \pmod m$.
Then the number of permutations $\pi$ of $\{0, \dots, n-1\}$ that $\mathrm{CSL}_n$ guesses in
exactly three guesses, with the second guess being the first guess that has a correct position,
is strictly smaller than the number of permutations $\pi$ that $S$ guesses in exactly three
guesses with the second guess being the first guess that has a correct position.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 16 (`jis-2026-26.1.7-thm-16`). -/
public theorem_wanted card_firstCorrectAt_two_cyclicShiftLeft_lt (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : IsInductivePermWordleStrategy n S)
    (hne : S n ≠ (finRotate n).symm) :
    Nat.card {π : Equiv.Perm (Fin n) //
        PermWordleSolvedIn (cyclicShiftLeftStrategy n) π 3 ∧
          PermWordleFirstCorrectAt (cyclicShiftLeftStrategy n) π 2} <
      Nat.card {π : Equiv.Perm (Fin n) //
        PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 2}

end

end MetaMathlibExt
