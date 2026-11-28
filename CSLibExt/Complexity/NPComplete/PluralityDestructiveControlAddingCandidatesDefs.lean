/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLURALITY DESTRUCTIVE CONTROL BY ADDING CANDIDATES: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PluralityConstructiveControlAddingCandidatesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PluralityDestructiveControlAddingCandidates

open PluralityConstructiveControlDeletingCandidates (IsUniquePluralityWinner)
open PluralityConstructiveControlAddingCandidates
  (PluralityConstructiveControlAddingCandidatesInstance)

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

end MetaMathlibExt.Complexity.NPComplete.PluralityDestructiveControlAddingCandidates
