/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLURALITY CONSTRUCTIVE CONTROL BY ADDING CANDIDATES: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PluralityConstructiveControlDeletingCandidatesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PluralityConstructiveControlAddingCandidates

open PluralityConstructiveControlDeletingCandidates (IsUniquePluralityWinner)

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

end MetaMathlibExt.Complexity.NPComplete.PluralityConstructiveControlAddingCandidates
