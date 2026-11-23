/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLURALITY DESTRUCTIVE CONTROL BY ADDING CANDIDATES is NP-complete

Source:
E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, "Anyone but him: The complexity of
precluding an alternative", Artificial Intelligence 171 (2007), 255-285,
doi:10.1016/j.artint.2007.01.005 (plurality resists destructive control by adding an unlimited
number of candidates, unique-winner model);
P. Faliszewski, E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, "Llull and Copeland voting
computationally resist bribery and constructive control", Journal of Artificial Intelligence
Research 35 (2009), 275-341, doi:10.1613/jair.2697 (arXiv:0809.4484), Section 2.2 (the problem
E-DCAC, adding a limited number of candidates) and Table 1 (plurality resists DCAC; this follows
from the result for adding an unlimited number of candidates).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PluralityConstructiveControlAddingCandidatesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PluralityDestructiveControlAddingCandidates

open PluralityConstructiveControlDeletingCandidates (IsUniquePluralityWinner)
open PluralityConstructiveControlAddingCandidates
  (PluralityConstructiveControlAddingCandidatesInstance)

/-!
# PLURALITY DESTRUCTIVE CONTROL BY ADDING CANDIDATES is NP-complete

INSTANCE: disjoint sets `C` (registered candidates) and `D` (spoiler candidates), a collection `V`
of voters specified via their preference lists over `C ∪ D`, a distinguished candidate `p ∈ C`,
and a nonnegative integer `k`. QUESTION: is there a subset `E ⊆ D` with `|E| ≤ k` such that `p` is
not the unique winner of the plurality election with voters `V` and candidates `C ∪ E`?

This is the destructive counterpart of
`WantedExt.Complexity.NPComplete.PluralityConstructiveControlAddingCandidatesWanted`, with the
same instance type and well-formedness condition: candidates are `0, …, m - 1`, `C` is given as
a list, `D` consists of the other candidates, `p ∈ C`, and each voter's list contains every
candidate exactly once, most preferred first. The election on `C ∪ E` restricts every list to
`C ∪ E`, and plurality and the unique-winner condition are
`PluralityConstructiveControlDeletingCandidates.IsUniquePluralityWinner`: `p` receives strictly
more first places among the present candidates than every other present candidate. `E = ∅` is
allowed, so an instance where `p` already is not the unique winner is a yes-instance. Hemaspaandra,
Hemaspaandra and Rothe (2007) prove the version without the bound `k` NP-complete; it is the
case `k = |D|`, so the bounded version is NP-hard as well. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Adding some set `E` of at most `k` spoiler candidates makes `p` not the unique plurality
winner of `C ∪ E`. -/
def PluralityDestructiveControlAddingCandidatesFeasible
    (i : PluralityConstructiveControlAddingCandidatesInstance) : Prop :=
  ∃ E : Finset ℕ, E ⊆ Finset.range i.1 \ i.2.1.toFinset ∧ E.card ≤ i.2.2.2.2 ∧
    ¬ IsUniquePluralityWinner i.2.2.2.1 (i.2.1.toFinset ∪ E) i.2.2.1

open Classical in
/-- PLURALITY DESTRUCTIVE CONTROL BY ADDING CANDIDATES as a decision problem over bitstrings. -/
noncomputable def pluralityDestructiveControlAddingCandidatesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PluralityConstructiveControlAddingCandidatesInstance) x with
  | some i => decide (PluralityConstructiveControlAddingCandidates.WellFormed i ∧
      PluralityDestructiveControlAddingCandidatesFeasible i)
  | none => false

/-- **PLURALITY DESTRUCTIVE CONTROL BY ADDING CANDIDATES is NP-complete.** Source: Hemaspaandra,
Hemaspaandra and Rothe (2007); Faliszewski, Hemaspaandra, Hemaspaandra and Rothe (2009),
Table 1. -/
public theorem_wanted pluralityDestructiveControlAddingCandidates_npComplete :
    pluralityDestructiveControlAddingCandidatesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pluralityDestructiveControlAddingCandidatesDec

end MetaMathlibExt.Complexity.NPComplete.PluralityDestructiveControlAddingCandidates
