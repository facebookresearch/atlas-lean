/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLURALITY CONSTRUCTIVE CONTROL BY ADDING CANDIDATES is NP-complete

Source:
J. J. Bartholdi III, C. A. Tovey and M. A. Trick, "How hard is it to control an election?",
Mathematical and Computer Modelling 16 (1992), 27-40, doi:10.1016/0895-7177(92)90085-Y;
P. Faliszewski, E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, "Llull and Copeland voting
computationally resist bribery and constructive control", Journal of Artificial Intelligence
Research 35 (2009), 275-341, doi:10.1613/jair.2697 (arXiv:0809.4484), Section 2.2 (the problem
E-CCAC, adding a limited number of candidates) and Table 1 (plurality resists it in the
unique-winner model; this follows from Bartholdi, Tovey and Trick's result for adding an
unlimited number of candidates).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PluralityConstructiveControlDeletingCandidatesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PluralityConstructiveControlAddingCandidates

open PluralityConstructiveControlDeletingCandidates (IsUniquePluralityWinner)

/-!
# PLURALITY CONSTRUCTIVE CONTROL BY ADDING CANDIDATES is NP-complete

INSTANCE: disjoint sets `C` (registered candidates) and `D` (spoiler candidates), a collection `V`
of voters specified via their preference lists over `C ∪ D`, a distinguished candidate `p ∈ C`,
and a nonnegative integer `k`. QUESTION: is there a subset `E ⊆ D` with `|E| ≤ k` such that `p` is
the unique winner of the plurality election with voters `V` and candidates `C ∪ E`?

Candidates are `0, …, m - 1`; `C` is given as a list, and `D` consists of the other candidates.
Each voter's list contains every candidate exactly once, most preferred first, and the election on
`C ∪ E` restricts every list to `C ∪ E`. Plurality and the unique-winner condition are those of
`WantedExt.Complexity.NPComplete.PluralityConstructiveControlDeletingCandidatesWanted`
(`PluralityConstructiveControlDeletingCandidates.IsUniquePluralityWinner`): `p` receives strictly
more first places among the present candidates than every other present candidate. Binary
encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of candidates `m`, the registered candidates `C`, the distinguished
candidate `p`, the voters' preference lists (most preferred first), and the bound `k`. -/
abbrev PluralityConstructiveControlAddingCandidatesInstance :=
  ℕ × List ℕ × ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: the registered candidates are candidates, `p` is registered,
and every voter's list contains every candidate exactly once. -/
def WellFormed (i : PluralityConstructiveControlAddingCandidatesInstance) : Prop :=
  (∀ c ∈ i.2.1, c < i.1) ∧ i.2.2.1 ∈ i.2.1 ∧ ∀ l ∈ i.2.2.2.1, l.Perm (List.range i.1)

/-- Adding some set `E` of at most `k` spoiler candidates makes `p` the unique plurality winner
of `C ∪ E`. -/
def PluralityConstructiveControlAddingCandidatesFeasible
    (i : PluralityConstructiveControlAddingCandidatesInstance) : Prop :=
  ∃ E : Finset ℕ, E ⊆ Finset.range i.1 \ i.2.1.toFinset ∧ E.card ≤ i.2.2.2.2 ∧
    IsUniquePluralityWinner i.2.2.2.1 (i.2.1.toFinset ∪ E) i.2.2.1

open Classical in
/-- PLURALITY CONSTRUCTIVE CONTROL BY ADDING CANDIDATES as a decision problem over bitstrings. -/
noncomputable def pluralityConstructiveControlAddingCandidatesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PluralityConstructiveControlAddingCandidatesInstance) x with
  | some i => decide (WellFormed i ∧ PluralityConstructiveControlAddingCandidatesFeasible i)
  | none => false

/-- **PLURALITY CONSTRUCTIVE CONTROL BY ADDING CANDIDATES is NP-complete.** Source: Bartholdi,
Tovey and Trick (1992); Faliszewski, Hemaspaandra, Hemaspaandra and Rothe (2009), Table 1. -/
public theorem_wanted pluralityConstructiveControlAddingCandidates_npComplete :
    pluralityConstructiveControlAddingCandidatesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pluralityConstructiveControlAddingCandidatesDec

end MetaMathlibExt.Complexity.NPComplete.PluralityConstructiveControlAddingCandidates
