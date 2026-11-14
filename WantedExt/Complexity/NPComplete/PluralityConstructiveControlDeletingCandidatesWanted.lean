/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLURALITY CONSTRUCTIVE CONTROL BY DELETING CANDIDATES is NP-complete

Source:
J. J. Bartholdi III, C. A. Tovey and M. A. Trick, "How hard is it to control an election?",
Mathematical and Computer Modelling 16 (1992), 27-40, doi:10.1016/0895-7177(92)90085-Y;
P. Faliszewski, E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, "Llull and Copeland voting
computationally resist bribery and constructive control", Journal of Artificial Intelligence
Research 35 (2009), 275-341, doi:10.1613/jair.2697 (arXiv:0809.4484), Section 2 (plurality,
the problem E-CCDC) and Table 1 (plurality resists constructive control by deleting candidates in
the unique-winner model, due to Bartholdi, Tovey and Trick).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PluralityConstructiveControlDeletingCandidates

/-!
# PLURALITY CONSTRUCTIVE CONTROL BY DELETING CANDIDATES is NP-complete

INSTANCE: a set `C` of candidates, a collection `V` of voters represented via preference lists
over `C`, a distinguished candidate `p ∈ C`, and a nonnegative integer `k`. QUESTION: is it
possible, by deleting at most `k` candidates other than `p`, to make `p` the unique winner of the
resulting plurality election?

Plurality elects the candidates that are ranked first by the largest number of voters; after
deleting candidates, each voter's preference list is restricted to the remaining candidates, so
a voter's vote goes to the first remaining candidate of the list. `p` is the unique winner when
it receives strictly more votes than every other remaining candidate (Bartholdi, Tovey and
Trick's unique-winner model). Candidates are `0, …, m - 1`; each voter's list contains every
candidate exactly once, most preferred first; the voters form a list (a multiset). Binary
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

/-- An instance: the number of candidates `m`, the distinguished candidate `p`, the voters'
preference lists (most preferred first), and the bound `k`. -/
abbrev PluralityConstructiveControlDeletingCandidatesInstance := ℕ × ℕ × List (List ℕ) × ℕ

/-- The plurality score of `a` among the remaining candidates `S`: the number of voters whose
first remaining candidate is `a`. -/
def pluralityScore (V : List (List ℕ)) (S : Finset ℕ) (a : ℕ) : ℕ :=
  (V.filter fun l => l.find? (· ∈ S) = some a).length

/-- `p` is the unique plurality winner among the remaining candidates `S`. -/
def IsUniquePluralityWinner (V : List (List ℕ)) (S : Finset ℕ) (p : ℕ) : Prop :=
  p ∈ S ∧ ∀ a ∈ S, a ≠ p → pluralityScore V S a < pluralityScore V S p

/-- Well-formedness of an instance: `p` is a candidate, and every voter's list contains every
candidate exactly once. -/
def WellFormed (i : PluralityConstructiveControlDeletingCandidatesInstance) : Prop :=
  i.2.1 < i.1 ∧ ∀ l ∈ i.2.2.1, l.Perm (List.range i.1)

/-- Deleting some set `E` of at most `k` candidates other than `p` makes `p` the unique
plurality winner of the remaining candidates. -/
def PluralityConstructiveControlDeletingCandidatesFeasible
    (i : PluralityConstructiveControlDeletingCandidatesInstance) : Prop :=
  ∃ E : Finset ℕ, E ⊆ Finset.range i.1 ∧ i.2.1 ∉ E ∧ E.card ≤ i.2.2.2 ∧
    IsUniquePluralityWinner i.2.2.1 (Finset.range i.1 \ E) i.2.1

open Classical in
/-- PLURALITY CONSTRUCTIVE CONTROL BY DELETING CANDIDATES as a decision problem over
bitstrings. -/
noncomputable def pluralityConstructiveControlDeletingCandidatesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PluralityConstructiveControlDeletingCandidatesInstance) x with
  | some i => decide (WellFormed i ∧ PluralityConstructiveControlDeletingCandidatesFeasible i)
  | none => false

/-- **PLURALITY CONSTRUCTIVE CONTROL BY DELETING CANDIDATES is NP-complete.** Source:
Bartholdi, Tovey and Trick (1992); Faliszewski, Hemaspaandra, Hemaspaandra and Rothe (2009),
Table 1. -/
public theorem_wanted pluralityConstructiveControlDeletingCandidates_npComplete :
    pluralityConstructiveControlDeletingCandidatesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pluralityConstructiveControlDeletingCandidatesDec

end MetaMathlibExt.Complexity.NPComplete.PluralityConstructiveControlDeletingCandidates
