/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERSECTION PATTERN with all diagonal entries 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), p. 222, problem [SP9] INTERSECTION PATTERN
(comment: remains NP-complete even if all `a_ii = 3`; reference: [Chvátal, 1978]);
V. Chvátal, "Recognizing intersection patterns", Annals of Discrete Mathematics 8 (1980),
249-251, doi:10.1016/S0167-5060(08)70883-5.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IntersectionPatternDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionPatternDiagonalThree

open MetaMathlibExt.Complexity.NPComplete.IntersectionPattern

/-- Well-formedness of an instance: the matrix is square and every diagonal entry is `3`. -/
def WellFormed (A : IntersectionPatternInstance) : Prop :=
  IntersectionPattern.WellFormed A ∧ ∀ i : Fin A.length, (A.getD i []).getD i 0 = 3

open Classical in
/-- INTERSECTION PATTERN with all diagonal entries 3 as a decision problem over bitstrings. -/
noncomputable def intersectionPatternDiagonalThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntersectionPatternInstance) x with
  | some A => decide (WellFormed A ∧ IntersectionPatternFeasible A)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntersectionPatternDiagonalThree
