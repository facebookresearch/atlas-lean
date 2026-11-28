/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-DIMENSIONAL MATCHING with at most three occurrences per element: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP1] 3-DIMENSIONAL MATCHING, p. 221,
comment: "Also remains NP-complete if no element occurs in more than three triples, but is
solvable in polynomial time if no element occurs in more than two triples [Garey and Johnson,
——]" (unpublished; the result and its attribution are those recorded by Garey and Johnson);
M. E. Dyer and A. M. Frieze, "Planar 3DM is NP-complete", Journal of Algorithms 7(2) (1986),
174-184, doi:10.1016/0196-6774(86)90002-7.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ThreeDimensionalMatchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatchingThreeOccurrences

open MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching
  (ThreeDimensionalMatchingInstance ThreeDimensionalMatchingFeasible)

/-- An instance: the common size `q` of `W`, `X`, `Y` and the list of triples; this is the
3-DIMENSIONAL MATCHING instance type. -/
abbrev ThreeDimensionalMatchingThreeOccurrencesInstance := ThreeDimensionalMatchingInstance

/-- Well-formedness of an instance: a well-formed 3-DIMENSIONAL MATCHING instance (every
coordinate below `q`) whose triples are distinct, and in which every element of `W`, of `X`
and of `Y` occurs in at most three triples. -/
def WellFormed (i : ThreeDimensionalMatchingThreeOccurrencesInstance) : Prop :=
  ThreeDimensionalMatching.WellFormed i ∧ i.2.Nodup ∧
    ∀ a < i.1, (i.2.filter fun t => t.1 = a).length ≤ 3 ∧
      (i.2.filter fun t => t.2.1 = a).length ≤ 3 ∧ (i.2.filter fun t => t.2.2 = a).length ≤ 3

/-- A matching of `q` triples (the 3-DIMENSIONAL MATCHING question). -/
def ThreeDimensionalMatchingThreeOccurrencesFeasible
    (i : ThreeDimensionalMatchingThreeOccurrencesInstance) : Prop :=
  ThreeDimensionalMatchingFeasible i

open Classical in
/-- 3-DIMENSIONAL MATCHING with at most three occurrences per element as a decision problem
over bitstrings. -/
noncomputable def threeDimensionalMatchingThreeOccurrencesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeDimensionalMatchingThreeOccurrencesInstance) x with
  | some i => decide (WellFormed i ∧ ThreeDimensionalMatchingThreeOccurrencesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatchingThreeOccurrences
