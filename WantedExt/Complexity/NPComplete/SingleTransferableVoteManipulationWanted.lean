/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE TRANSFERABLE VOTE MANIPULATION is NP-complete

Source:
J. J. Bartholdi III and J. B. Orlin, "Single transferable vote resists strategic voting",
Social Choice and Welfare 8 (1991), 341-354, doi:10.1007/BF00183045
(Theorem 1: EFFECTIVE PREFERENCE is NP-complete under Successive Elimination).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.MinMax

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleTransferableVoteManipulation

/-!
# SINGLE TRANSFERABLE VOTE MANIPULATION is NP-complete

Bartholdi and Orlin's EFFECTIVE PREFERENCE problem for single-winner STV:
"GIVEN: A set `C` of candidates; a distinguished candidate `c`; and the set `V` of sincere,
transitive, strict, and complete preferences of the voters. QUESTION: Is there a preference
ordering on `C` that when tallied with the preferences of `V` will ensure the election of `c`?"

Single-winner STV is the voting scheme of the source's Theorem 1, "successively eliminating a
candidate with the fewest votes and reallocating his support": each ballot counts for its most
preferred candidate that has not been eliminated, a candidate with the fewest such votes is
eliminated, and this repeats until one candidate, the winner, remains. (A candidate with more
than half of the ballots is never one with the fewest votes while two or more remain, so the
source's early election of a candidate reaching the quota `⌊|V| / 2⌋ + 1` elects the same
winner.) Ties for the fewest votes are broken by a fixed order of the candidates: the instance
lists the candidates, and among the tied candidates the one listed first is eliminated. The
source leaves tie-breaking open and observes that the election is in NP because a preference
"can be verified in polynomial time by tallying the election", which needs a deterministic
tally.

Candidates are natural-number names listed without repetition; a preference is a list of all
candidates, most preferred first (a permutation of the candidate list). The strategic voter's
preference is a permutation of the candidate list as well, tallied together with `V`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SINGLE TRANSFERABLE VOTE MANIPULATION is NP-complete.** Source: Bartholdi and Orlin
(1991), Theorem 1. -/
public theorem_wanted singleTransferableVoteManipulation_npComplete :
    singleTransferableVoteManipulationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleTransferableVoteManipulationDec

end MetaMathlibExt.Complexity.NPComplete.SingleTransferableVoteManipulation
