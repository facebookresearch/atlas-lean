/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE TRANSFERABLE VOTE MANIPULATION: definitions

Source:
J. J. Bartholdi III and J. B. Orlin, "Single transferable vote resists strategic voting",
Social Choice and Welfare 8 (1991), 341-354, doi:10.1007/BF00183045
(Theorem 1: EFFECTIVE PREFERENCE is NP-complete under Successive Elimination).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.MinMax

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleTransferableVoteManipulation

/-- An instance: the candidates `C` (in the fixed tie-breaking order), the sincere preferences
`V` (each a list of all candidates, most preferred first), and the distinguished candidate `c`. -/
abbrev SingleTransferableVoteManipulationInstance := List ℕ × List (List ℕ) × ℕ

/-- The candidate a ballot counts for while the candidates `R` remain: its most preferred
candidate in `R`. -/
def top (R : List ℕ) (b : List ℕ) : Option ℕ :=
  b.find? (· ∈ R)

/-- The number of ballots counting for candidate `a` while the candidates `R` remain. -/
def votes (ballots : List (List ℕ)) (R : List ℕ) (a : ℕ) : ℕ :=
  ballots.countP fun b => top R b = some a

/-- One elimination round: remove the remaining candidate with the fewest votes, the one listed
first among those tied (Mathlib's `List.argmin` returns the first minimizer). -/
def eliminate (ballots : List (List ℕ)) (R : List ℕ) : List ℕ :=
  match R.argmin (votes ballots R) with
  | some a => R.erase a
  | none => R

/-- The single-winner STV winner: the last remaining candidate after `|C| - 1` eliminations. -/
def winner (C : List ℕ) (ballots : List (List ℕ)) : Option ℕ :=
  ((eliminate ballots)^[C.length - 1] C).head?

/-- Well-formedness of an instance: the candidates are listed without repetition, `c` is a
candidate, and every sincere preference ranks every candidate exactly once. -/
def WellFormed (i : SingleTransferableVoteManipulationInstance) : Prop :=
  i.1.Nodup ∧ i.2.2 ∈ i.1 ∧ ∀ b ∈ i.2.1, b.Perm i.1

/-- Some preference ordering `p` on `C`, tallied with `V`, makes `c` the STV winner. -/
def SingleTransferableVoteManipulationFeasible
    (i : SingleTransferableVoteManipulationInstance) : Prop :=
  ∃ p : List ℕ, p.Perm i.1 ∧ winner i.1 (p :: i.2.1) = some i.2.2

open Classical in
/-- SINGLE TRANSFERABLE VOTE MANIPULATION as a decision problem over bitstrings. -/
noncomputable def singleTransferableVoteManipulationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleTransferableVoteManipulationInstance) x with
  | some i => decide (WellFormed i ∧ SingleTransferableVoteManipulationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SingleTransferableVoteManipulation
