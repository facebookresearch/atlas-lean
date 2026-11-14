/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BANKS WINNER is NP-complete

Source:
G. J. Woeginger, "Banks winners in tournaments are difficult to recognize", Social Choice and
Welfare 20 (2003), 523-528, doi:10.1007/s003550200197 (deciding whether a given vertex is a
Banks winner is NP-complete; reduction from graph 3-colorability);
F. Brandt, F. Fischer and P. Harrenstein, "Recognizing members of the tournament equilibrium
set is NP-hard", arXiv:0711.2961 (2007), Definition 1 (the Banks set) and Section 4 (an
alternative proof of Woeginger's result, by a reduction from 3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Data.Finset.Insert
public import Mathlib.Order.Defs.Unbundled
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BanksWinner

/-!
# BANKS WINNER is NP-complete

INSTANCE: a tournament `T` on a finite vertex set `C` (an irreflexive, antisymmetric and
complete dominance relation), and a vertex `c ∈ C`.
QUESTION: is `c` a Banks winner of `T`, i.e., is `c` the top vertex (the vertex dominating all
others) of some maximal transitive subtournament of `T`? A set `X ⊆ C` is transitive when the
dominance relation is transitive on `X`, and maximal when no transitive set strictly contains it.

The vertices are `Fin n`, and the tournament is its list of arcs: `(a, b)` means that `a`
dominates `b`. Maximality is Mathlib's `Maximal` for inclusion of `Finset`s.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n = |C|` of vertices, the arcs of the tournament, and the vertex
`c`. -/
abbrev BanksWinnerInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the arc list has no repeated arc, every arc joins two
distinct vertices of `C` and its reverse is not an arc, every two distinct vertices are joined
by an arc (so `T` is a tournament), and `c ∈ C`. -/
def WellFormed (i : BanksWinnerInstance) : Prop :=
  i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ a < i.1, ∀ b < i.1, a ≠ b → (a, b) ∈ i.2.1 ∨ (b, a) ∈ i.2.1) ∧
    i.2.2 < i.1

/-- `a` dominates `b` in the tournament of the instance. -/
def Dominates (i : BanksWinnerInstance) (a b : Fin i.1) : Prop :=
  ((a : ℕ), (b : ℕ)) ∈ i.2.1

/-- The dominance relation is transitive on `X`. -/
def IsTransitiveSet (i : BanksWinnerInstance) (X : Finset (Fin i.1)) : Prop :=
  ∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, Dominates i a b → Dominates i b d → Dominates i a d

/-- `c` is the top vertex of some maximal transitive set of the tournament. -/
def BanksWinnerFeasible (i : BanksWinnerInstance) : Prop :=
  ∃ X : Finset (Fin i.1), Maximal (IsTransitiveSet i) X ∧
    ∃ c ∈ X, (c : ℕ) = i.2.2 ∧ ∀ v ∈ X, v ≠ c → Dominates i c v

open Classical in
/-- BANKS WINNER as a decision problem over bitstrings. -/
noncomputable def banksWinnerDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BanksWinnerInstance) x with
  | some i => decide (WellFormed i ∧ BanksWinnerFeasible i)
  | none => false

/-- **BANKS WINNER is NP-complete.** Source: Woeginger (2003); Brandt, Fischer and Harrenstein
(2007). -/
public theorem_wanted banksWinner_npComplete :
    banksWinnerDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L banksWinnerDec

end MetaMathlibExt.Complexity.NPComplete.BanksWinner
