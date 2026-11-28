/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-DIMENSIONAL CONSECUTIVE SETS with sets of size at most 5: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR19] 2-DIMENSIONAL CONSECUTIVE
SETS, p. 230, comment: "Remains NP-complete if all `Σⱼ ∈ C` have `|Σⱼ| ≤ 5`, but is solvable in
polynomial time if all `Σⱼ ∈ C` have `|Σⱼ| ≤ 2`" (the entry's reference is [Lipsky, 1977b]);
W. Lipski, Jr., "One more polynomial complete consecutive retrieval problem", Information
Processing Letters 6 (1977), 91-93, doi:10.1016/0020-0190(77)90034-5 (Garey and Johnson's
reference for [SR19]; its text was not available to check the bound `5`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsSizeFive

/-- Well-formedness of an instance: it is a well-formed 2-DIMENSIONAL CONSECUTIVE SETS instance
(every subset lists distinct symbols of the alphabet), and every subset has at most `5`
elements. -/
def WellFormed (i : TwoDimensionalConsecutiveSets.TwoDimensionalConsecutiveSetsInstance) :
    Prop :=
  TwoDimensionalConsecutiveSets.WellFormed i ∧ ∀ S ∈ i.2, S.length ≤ 5

open Classical in
/-- 2-DIMENSIONAL CONSECUTIVE SETS with sets of size at most 5 as a decision problem over
bitstrings. -/
noncomputable def twoDimensionalConsecutiveSetsSizeFiveDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoDimensionalConsecutiveSets.TwoDimensionalConsecutiveSetsInstance) x with
  | some i => decide (WellFormed i ∧
      TwoDimensionalConsecutiveSets.TwoDimensionalConsecutiveSetsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsSizeFive
