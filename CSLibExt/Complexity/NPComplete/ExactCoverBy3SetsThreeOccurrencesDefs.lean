/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXACT COVER BY 3-SETS with at most three occurrences per element: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 221, problem [SP2] EXACT COVER BY 3-SETS
(X3C) (comment: remains NP-complete if no element occurs in more than three subsets
[Garey and Johnson, unpublished]);
T. F. Gonzalez, "Clustering to minimize the maximum intercluster distance", Theoretical
Computer Science 38 (1985), 293-306, doi:10.1016/0304-3975(85)90224-5 (NP-completeness when
every element occurs in exactly three subsets).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ExactCoverBy3SetsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3SetsThreeOccurrences

open MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3Sets

/-- Well-formedness of an instance: it is a well-formed X3C instance, every member of `C` is
listed in increasing order, no member is listed twice, and every element of `X` occurs in at
most three members of `C`. -/
def WellFormed (i : ExactCoverBy3SetsInstance) : Prop :=
  ExactCoverBy3Sets.WellFormed i ∧ (∀ s ∈ i.2, s.Pairwise (· < ·)) ∧ i.2.Nodup ∧
    ∀ x < 3 * i.1, (i.2.filter fun s => x ∈ s).length ≤ 3

open Classical in
/-- EXACT COVER BY 3-SETS with at most three occurrences per element as a decision problem over
bitstrings. -/
noncomputable def exactCoverBy3SetsThreeOccurrencesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExactCoverBy3SetsInstance) x with
  | some i => decide (WellFormed i ∧ ExactCoverBy3SetsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3SetsThreeOccurrences
