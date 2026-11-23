/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IWD-STRATEGY-ELIMINATION (eliminability by iterated weak dominance) is NP-complete

Source:
V. Conitzer and T. Sandholm, "Complexity of (iterated) dominance", Proceedings of the 6th ACM
Conference on Electronic Commerce (EC 2005), 88-97, doi:10.1145/1064009.1064019,
Definition 3 and Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IteratedWeakDominance

/-!
# IWD-STRATEGY-ELIMINATION (eliminability by iterated weak dominance) is NP-complete

A two-player normal-form game: the row player has pure strategies `0, …, m - 1`, the column
player has pure strategies `0, …, n - 1`, and each player has a utility for each pair of pure
strategies. A strategy `σ'` of a player is weakly dominated by a strategy `σ` of the same
player if `σ` gives that player at least the utility of `σ'` against every strategy of the
opponent and strictly more against at least one. In iterated weak dominance, strategies are
eliminated one at a time; at each step the eliminated strategy must be weakly dominated by a
strategy of the same player that has not been eliminated, with the comparison made only
against the opponent's strategies that have not been eliminated. Given a game and a
distinguished pure strategy `σ*`, IWD-STRATEGY-ELIMINATION asks whether some such sequence of
eliminations eliminates `σ*` (Conitzer and Sandholm 2005, Definition 3). Their Theorem 1
proves it NP-complete even with two players and utilities in `{0, 1}`, whether or not
dominance by mixed strategies is allowed; this file states the two-player problem with
dominance by pure strategies and integer utilities.

Utilities are integers, each encoded as a pair of naturals `(positive part, negative part)`
representing their difference, as in `ZeroOneILPWanted`. A state of the elimination is the
pair of sets of strategies not yet eliminated.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of row strategies, the number `n` of column strategies, the
utility table (row `r`, entry `c` holds the row player's and the column player's utilities at
`(r, c)`, each as a `(positive part, negative part)` pair), the player who owns the
distinguished strategy (`false`: row player, `true`: column player), and the index of the
distinguished strategy. -/
abbrev IteratedWeakDominanceInstance :=
  ℕ × ℕ × List (List ((ℕ × ℕ) × (ℕ × ℕ))) × Bool × ℕ

/-- The table entry at row `r`, column `c`. -/
def entry (i : IteratedWeakDominanceInstance) (r : Fin i.1) (c : Fin i.2.1) :
    (ℕ × ℕ) × (ℕ × ℕ) :=
  (i.2.2.1.getD r []).getD c ((0, 0), (0, 0))

/-- The row player's utility at `(r, c)`. -/
def rowUtility (i : IteratedWeakDominanceInstance) (r : Fin i.1) (c : Fin i.2.1) : ℤ :=
  ((entry i r c).1.1 : ℤ) - (entry i r c).1.2

/-- The column player's utility at `(r, c)`. -/
def colUtility (i : IteratedWeakDominanceInstance) (r : Fin i.1) (c : Fin i.2.1) : ℤ :=
  ((entry i r c).2.1 : ℤ) - (entry i r c).2.2

/-- Row strategy `r` is weakly dominated by a row strategy in `R` when the column player is
restricted to `C`. -/
def RowWeaklyDominated (i : IteratedWeakDominanceInstance) (R : Finset (Fin i.1))
    (C : Finset (Fin i.2.1)) (r : Fin i.1) : Prop :=
  ∃ r' ∈ R, (∀ c ∈ C, rowUtility i r c ≤ rowUtility i r' c) ∧
    ∃ c ∈ C, rowUtility i r c < rowUtility i r' c

/-- Column strategy `c` is weakly dominated by a column strategy in `C` when the row player
is restricted to `R`. -/
def ColWeaklyDominated (i : IteratedWeakDominanceInstance) (R : Finset (Fin i.1))
    (C : Finset (Fin i.2.1)) (c : Fin i.2.1) : Prop :=
  ∃ c' ∈ C, (∀ r ∈ R, colUtility i r c ≤ colUtility i r c') ∧
    ∃ r ∈ R, colUtility i r c < colUtility i r c'

/-- One elimination step from the surviving strategies `S = (R, C)` to `T`: remove one row
strategy of `R` weakly dominated within `S`, or one column strategy of `C` weakly dominated
within `S`. -/
def EliminationStep (i : IteratedWeakDominanceInstance)
    (S T : Finset (Fin i.1) × Finset (Fin i.2.1)) : Prop :=
  (∃ r ∈ S.1, RowWeaklyDominated i S.1 S.2 r ∧ T = (S.1.erase r, S.2)) ∨
    (∃ c ∈ S.2, ColWeaklyDominated i S.1 S.2 c ∧ T = (S.1, S.2.erase c))

/-- Well-formedness of an instance: both players have at least one strategy, the table has
`m` rows of `n` entries, and the distinguished strategy is a strategy of its player. -/
def WellFormed (i : IteratedWeakDominanceInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ i.2.2.1.length = i.1 ∧ (∀ row ∈ i.2.2.1, row.length = i.2.1) ∧
    (if i.2.2.2.1 then i.2.2.2.2 < i.2.1 else i.2.2.2.2 < i.1)

/-- Some sequence of iterated weak dominance steps, starting from the whole game, reaches a
state in which the distinguished strategy has been eliminated. -/
def IteratedWeakDominanceFeasible (i : IteratedWeakDominanceInstance) : Prop :=
  ∃ S, Relation.ReflTransGen (EliminationStep i) (Finset.univ, Finset.univ) S ∧
    if i.2.2.2.1 then ∀ c ∈ S.2, (c : ℕ) ≠ i.2.2.2.2 else ∀ r ∈ S.1, (r : ℕ) ≠ i.2.2.2.2

open Classical in
/-- IWD-STRATEGY-ELIMINATION as a decision problem over bitstrings. -/
noncomputable def iteratedWeakDominanceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IteratedWeakDominanceInstance) x with
  | some i => decide (WellFormed i ∧ IteratedWeakDominanceFeasible i)
  | none => false

/-- **IWD-STRATEGY-ELIMINATION is NP-complete** (two players, dominance by pure strategies).
Source: Conitzer and Sandholm (2005), Theorem 1. -/
public theorem_wanted iteratedWeakDominance_npComplete :
    iteratedWeakDominanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L iteratedWeakDominanceDec

end MetaMathlibExt.Complexity.NPComplete.IteratedWeakDominance
