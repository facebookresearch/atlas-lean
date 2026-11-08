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

/-- A tournament on `Fin n`: `T i j = true` means `i`
beats `j`; every pair has exactly one winner and there
are no self-wins. -/
def IsTournament {n : ℕ} (T : Fin n → Fin n → Bool) :
    Prop :=
  (∀ i, T i i = false) ∧ ∀ i j, i ≠ j → T i j ≠ T j i

/-- The score (outdegree) of a player in a tournament. -/
def score {n : ℕ} (T : Fin n → Fin n → Bool) (i : Fin n) :
    ℕ :=
  (Finset.univ.filter (fun j => T i j)).card

/-- A tournament is reducible if some nonempty proper
set of players loses all games against the complement. -/
def IsReducible {n : ℕ} (T : Fin n → Fin n → Bool) :
    Prop :=
  ∃ S : Finset (Fin n), S.Nonempty ∧ S ≠ Finset.univ ∧
    ∀ i ∈ S, ∀ j, j ∉ S → T i j = false

/-- A circular triad: a 3-subset in which every vertex
has outdegree exactly `1` (a directed 3-cycle). -/
def IsCircularTriad {n : ℕ} (T : Fin n → Fin n → Bool)
    (S : Finset (Fin n)) : Prop :=
  S.card = 3 ∧
    ∀ i ∈ S, (S.filter (fun j => T i j)).card = 1

instance {n : ℕ} (T : Fin n → Fin n → Bool)
    (S : Finset (Fin n)) :
    Decidable (IsCircularTriad T S) :=
  inferInstanceAs (Decidable (S.card = 3 ∧
    ∀ i ∈ S, (S.filter (fun j => T i j)).card = 1))

/-- **Theorem 1**: the sequence `g(n) = n! * C(n-a+b, b)`
(`n ≥ a`) has exponential generating function
`x^a * (1 - x)^{-(b+1)}` (stated in the multiplied-out
form `(1 - x)^{b+1} * A(x) = x^a` over `ℚ`).

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Theorem 1. -/
theorem_wanted egf_factorial_choose (a b : ℕ) :
    (1 - PowerSeries.X) ^ (b + 1) *
        PowerSeries.mk (fun n =>
          if a ≤ n then (Nat.choose (n - a + b) b : ℚ)
          else 0)
      = PowerSeries.X ^ a

/-- **Theorem 4** (Landau, via Moon): a nondecreasing
sequence `s_1 ≤ ⋯ ≤ s_n` is the score sequence of a
tournament if and only if `∑_{i=1}^k s_i ≥ C(k, 2)` for
`1 ≤ k ≤ n`, with equality when `k = n`.

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

/-- **Theorem 5** (Moon): a tournament with score
sequence `s_1 ≤ ⋯ ≤ s_n` is reducible if and only if
`∑_{i=1}^k s_i = C(k, 2)` for some positive integer
`k < n`.

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

/-- **Theorem 6** (Moon): the number of circular triads
in a tournament with scores `s_1, …, s_n` is
`C(n, 3) - ∑_i C(s_i, 2)`.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Theorem 6. -/
theorem_wanted card_circularTriads (n : ℕ)
    (T : Fin n → Fin n → Bool) (hT : IsTournament T) :
    ((Finset.univ.powersetCard 3).filter
        (IsCircularTriad T)).card =
      Nat.choose n 3 - ∑ i, Nat.choose (score T i) 2

end MathlibExt.GraphTheory.TournamentScoreSequenceWanted
