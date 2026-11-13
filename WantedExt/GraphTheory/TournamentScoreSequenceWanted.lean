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

Propositions 2 and 3 are the sum and product rules for
exponential generating functions of labeled structures
whose counts depend only on the number of players.
`atomCount n d` is the paper's `N(n, d)` (non-trivial
atoms, i.e. irreducible tournaments on `n ≥ 2` players,
with `d` circular triads) and `tournamentCount n d` its
`g_d(n)`; Theorems 8 and 10 are stated with these.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

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


instance {n : ℕ} (T : Fin n → Fin n → Bool) :
    Decidable (IsTournament T) :=
  inferInstanceAs (Decidable ((∀ i, T i i = false) ∧
    ∀ i j, i ≠ j → T i j ≠ T j i))

instance {n : ℕ} (T : Fin n → Fin n → Bool) :
    Decidable (IsReducible T) :=
  inferInstanceAs (Decidable (∃ S : Finset (Fin n),
    S.Nonempty ∧ S ≠ Finset.univ ∧
      ∀ i ∈ S, ∀ j, j ∉ S → T i j = false))

/-- The number of circular triads of a tournament.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Section 2. -/
def circularTriadCount {n : ℕ} (T : Fin n → Fin n → Bool) :
    ℕ :=
  ((Finset.univ.powersetCard 3).filter
    (IsCircularTriad T)).card

/-- `g_d(n)`: the number of tournaments on the labeled
players `Fin n` with exactly `d` circular triads.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Section 1. -/
def tournamentCount (n d : ℕ) : ℕ :=
  (Finset.univ.filter (fun T : Fin n → Fin n → Bool =>
    IsTournament T ∧ circularTriadCount T = d)).card

/-- `N(n, d)`: the number of non-trivial atoms
(irreducible tournaments on `n ≥ 2` labeled players; the
single-node atom is trivial) with exactly `d` circular
triads.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Section 3. -/
def atomCount (n d : ℕ) : ℕ :=
  (Finset.univ.filter (fun T : Fin n → Fin n → Bool =>
    IsTournament T ∧ ¬ IsReducible T ∧ 1 < n ∧
      circularTriadCount T = d)).card

/-- `g_0(3) = 6` (the transitive tournaments) and
`g_1(3) = 2` (the two directed 3-cycles).

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Section 1. -/
theorem tournamentCount_three :
    tournamentCount 3 0 = 6 ∧ tournamentCount 3 1 = 2 := by
  decide +kernel

/-- `N(3, 1) = 2`: the two circular triads are the atoms
on three players (Table 1).

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Section 3, Table 1. -/
theorem atomCount_three_one : atomCount 3 1 = 2 := by
  decide +kernel

/-- The atomic generator `A_d(x) = ∑_n N(n, d) xⁿ / n!`.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Section 3. -/
noncomputable def atomicGenerator (d : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (atomCount n d : ℚ) / n.factorial

/-- **Proposition 2**: if `c_n = a_n + b_n` counts the
structures on `n` labeled players split into two disjoint
cases, then the exponential generating functions satisfy
`C(x) = A(x) + B(x)`.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Proposition 2
(`jis-2024-24.8.7-prop-2`). -/
theorem_wanted egf_add (a b c : ℕ → ℕ)
    (hc : ∀ n, c n = a n + b n) :
    PowerSeries.mk (fun n => (c n : ℚ) / n.factorial) =
      PowerSeries.mk (fun n => (a n : ℚ) / n.factorial) +
        PowerSeries.mk (fun n => (b n : ℚ) / n.factorial)

/-- **Proposition 3**: if `a_k` and `b_k` count the
`α`- and `β`-structures on `k` labeled players and `c_n`
counts the ways to split `{1, …, n}` into sets `S₁`, `S₂`
and place an `α`-structure on `S₁` and a `β`-structure on
`S₂` (so `c_n = ∑_{S₁ ⊆ [n]} a_{|S₁|} b_{n - |S₁|}`), then
`C(x) = A(x) B(x)` for the exponential generating
functions.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Proposition 3
(`jis-2024-24.8.7-prop-3`). -/
theorem_wanted egf_mul (a b c : ℕ → ℕ)
    (hc : ∀ n, c n = ∑ S ∈ (Finset.range n).powerset,
      a S.card * b (n - S.card)) :
    PowerSeries.mk (fun n => (c n : ℚ) / n.factorial) =
      PowerSeries.mk (fun n => (a n : ℚ) / n.factorial) *
        PowerSeries.mk (fun n => (b n : ℚ) / n.factorial)

/-- **Theorem 8**: for `d ≥ 1`,
`A_d(x) = ∑_{k=L(d)}^{d+2} N(k, d) x^k / k!`, where
`L(d) = min(I_o(d), I_e(d))` with `I_o(d)` (`I_e(d)`) the
least positive odd (even) integer solution of
`x³ - x - 24d ≥ 0` (`x³ - 4x - 24d ≥ 0`). Stated as the
equivalent support condition `N(k, d) ≠ 0 →
L(d) ≤ k ≤ d + 2`, with `L(d) ≤ k` written as the
existence of a positive `j ≤ k` solving the odd or the
even inequality (both cubics increase on the positive
integers).

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Theorem 8
(`jis-2024-24.8.7-thm-8`). -/
theorem_wanted atomCount_ne_zero_bounds (d k : ℕ) (hd : 1 ≤ d)
    (hk : atomCount k d ≠ 0) :
    k ≤ d + 2 ∧ ∃ j : ℕ, 0 < j ∧ j ≤ k ∧
      ((Odd j ∧ 24 * (d : ℤ) ≤ (j : ℤ) ^ 3 - j) ∨
        (Even j ∧ 24 * (d : ℤ) ≤ (j : ℤ) ^ 3 - 4 * j))

/-- **Theorem 10**: the exponential generating function
`G_d(x) = ∑_n g_d(n) xⁿ / n!` of tournaments with `d`
circular triads is
`∑_{r ∈ P_d} r!/(r₁! ⋯ r_d!) (1 - x)^{-(1+r)}
  ∏_{i=1}^d A_i(x)^{r_i}`, the sum over partitions of `d`
with multiplicities `r_i` and size `r`. Stated for every
`d` (at `d = 0` both sides are `1/(1 - x)`), with the
`n = 0` coefficient `g_d(0)` included.

Source: Ian R. Harris and Ryan P. A. McShane, "Counting
Tournaments with a Specified Number of Circular
Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Theorem 10
(`jis-2024-24.8.7-thm-10`). -/
theorem_wanted tournament_egf (d : ℕ) :
    PowerSeries.mk (fun n => (tournamentCount n d : ℚ) / n.factorial) =
      ∑ p : Nat.Partition d,
        ((p.parts.card.factorial : ℚ) /
            ∏ i ∈ p.parts.toFinset, ((p.parts.count i).factorial : ℚ)) •
          ((1 - PowerSeries.X)⁻¹ ^ (1 + p.parts.card) *
            (p.parts.map atomicGenerator).prod)

end MathlibExt.GraphTheory.TournamentScoreSequenceWanted
