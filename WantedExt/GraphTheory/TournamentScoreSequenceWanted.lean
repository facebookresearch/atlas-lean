/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Counting tournaments with a specified number of circular triads

Statements from Ian R. Harris and Ryan P. A. McShane,
"Counting Tournaments with a Specified Number of
Circular Triads", *Journal of Integer Sequences* 27
(2024), Article 24.8.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/McShane/mcshane1.html>).

A tournament on `Fin n` is encoded by `T i j = true`
for "`i` beats `j`", with `score T i` the outdegree of
`i`. A circular triad is a 3-subset in which every
vertex has outdegree exactly `1` (a directed 3-cycle,
as opposed to a transitive triple with outdegrees
`2, 1, 0`), and reducibility is the existence of a
nonempty proper subset losing all its games against
the complement. Landau's theorem, the reducibility
criterion, and the circular-triad count were verified
exhaustively/randomly for small `n` against these
definitions.

Not stated (see the source audit table): Propositions
2 and 3 (abstract structure counts) and Theorems 8 and
10 (which use the paper's `N(k, d)` and `P_d`, not
defined in the extracted statements).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.GraphTheory.TournamentScoreSequenceWanted

/-- **Tournament.** A tournament on the players $1, \dots, n$ is a binary relation $T$, where
$T(i, j)$ means that $i$ beats $j$, such that no player beats itself and for any two distinct
players $i$ and $j$ exactly one of $T(i, j)$ and $T(j, i)$ holds. -/
def IsTournament {n : ℕ} (T : Fin n → Fin n → Bool) :
    Prop :=
  (∀ i, T i i = false) ∧ ∀ i j, i ≠ j → T i j ≠ T j i

/-- **Score of a player.** Let $T$ be a binary relation on the players $1, \dots, n$, where
$T(i, j)$ means that $i$ beats $j$. The score of a player $i$ is the number of players $j$ such
that $T(i, j)$ holds, that is, the number of players that $i$ beats.

In a tournament this is the outdegree of $i$. -/
def score {n : ℕ} (T : Fin n → Fin n → Bool) (i : Fin n) :
    ℕ :=
  (Finset.univ.filter (fun j => T i j)).card

/-- A tournament is reducible if some nonempty proper
set of players loses all games against the complement. -/
def IsReducible {n : ℕ} (T : Fin n → Fin n → Bool) :
    Prop :=
  ∃ S : Finset (Fin n), S.Nonempty ∧ S ≠ Finset.univ ∧
    ∀ i ∈ S, ∀ j, j ∉ S → T i j = false

/-- **Circular triad.** Let $T$ be a binary relation on the players $1, \dots, n$, where
$T(i, j)$ means that $i$ beats $j$. A set $S$ of players is a circular triad of $T$ if $S$ has
exactly three elements and every $i \in S$ beats exactly one $j \in S$.

In a tournament this means that the three players form a directed $3$-cycle. -/
def IsCircularTriad {n : ℕ} (T : Fin n → Fin n → Bool)
    (S : Finset (Fin n)) : Prop :=
  S.card = 3 ∧
    ∀ i ∈ S, (S.filter (fun j => T i j)).card = 1

instance {n : ℕ} (T : Fin n → Fin n → Bool)
    (S : Finset (Fin n)) :
    Decidable (IsCircularTriad T S) :=
  inferInstanceAs (Decidable (S.card = 3 ∧
    ∀ i ∈ S, (S.filter (fun j => T i j)).card = 1))

/-- **Exponential generating function of a shifted binomial sequence.** For natural numbers $a$
and $b$, let $g(n) = n! \binom{n-a+b}{b}$ for $n \ge a$ and $g(n) = 0$ for $n < a$, and let
$A(x) = \sum_{n \ge 0} g(n) x^n / n!$ be its exponential generating function, a formal power
series over $\mathbb{Q}$. Then $(1 - x)^{b+1} A(x) = x^a$; equivalently,
$A(x) = x^a (1 - x)^{-(b+1)}$.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Theorem 1. -/
theorem_wanted egf_factorial_choose (a b : ℕ) :
    (1 - PowerSeries.X) ^ (b + 1) *
        PowerSeries.mk (fun n =>
          if a ≤ n then (Nat.choose (n - a + b) b : ℚ)
          else 0)
      = PowerSeries.X ^ a

/-- **Landau's theorem on score sequences.** Let $s_1 \le s_2 \le \dots \le s_n$ be a
nondecreasing sequence of natural numbers. There is a tournament on $n$ players in which player
$i$ has score $s_i$ for every $i$ if and only if $\sum_{i=1}^{k} s_i \ge \binom{k}{2}$ for every
$k$ with $1 \le k \le n$ and $\sum_{i=1}^{n} s_i = \binom{n}{2}$.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Theorem 4. -/
theorem_wanted landau_score_sequence (n : ℕ)
    (s : Fin n → ℕ)
    (hs : ∀ i j : Fin n, i ≤ j → s i ≤ s j) :
    (∃ T : Fin n → Fin n → Bool, IsTournament T ∧
      ∀ i, score T i = s i) ↔
    (∀ k : ℕ, ∀ hk : k ≤ n, 1 ≤ k →
      Nat.choose k 2 ≤
        ∑ i : Fin k, s (Fin.castLE hk i)) ∧
    (∑ i, s i) = Nat.choose n 2

/-- **Moon's reducibility criterion.** Let $T$ be a tournament on $n$ players in which the score
$s_i$ of player $i$ satisfies $s_1 \le s_2 \le \dots \le s_n$. Then $T$ is reducible if and only
if $\sum_{i=1}^{k} s_i = \binom{k}{2}$ for some integer $k$ with $1 \le k < n$.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Theorem 5. -/
theorem_wanted isReducible_iff (n : ℕ)
    (T : Fin n → Fin n → Bool) (s : Fin n → ℕ)
    (hT : IsTournament T)
    (hs : ∀ i j : Fin n, i ≤ j → s i ≤ s j)
    (hscore : ∀ i, score T i = s i) :
    IsReducible T ↔
      ∃ k : ℕ, ∃ hk : k ≤ n, 1 ≤ k ∧ k < n ∧
        (∑ i : Fin k, s (Fin.castLE hk i)) =
          Nat.choose k 2

/-- **Moon's count of circular triads.** In a tournament on $n$ players with scores
$s_1, \dots, s_n$, the number of circular triads is
$\binom{n}{3} - \sum_{i=1}^{n} \binom{s_i}{2}$.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Theorem 6. -/
theorem_wanted card_circularTriads (n : ℕ)
    (T : Fin n → Fin n → Bool) (hT : IsTournament T) :
    ((Finset.univ.powersetCard 3).filter
        (IsCircularTriad T)).card =
      Nat.choose n 3 - ∑ i, Nat.choose (score T i) 2

end MathlibExt.GraphTheory.TournamentScoreSequenceWanted
