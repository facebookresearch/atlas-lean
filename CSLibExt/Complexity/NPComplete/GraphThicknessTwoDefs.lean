/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH THICKNESS 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN3];
A. Mansfield, "Determining the thickness of graphs is NP-hard", Mathematical Proceedings of the
Cambridge Philosophical Society 93 (1983), 9-23, doi:10.1017/S030500410006028X.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphThicknessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphThicknessTwo

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev GraphThicknessTwoInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH THICKNESS instance with the same graph and bound `K = 2`. -/
def withBound (i : GraphThicknessTwoInstance) : GraphThickness.GraphThicknessInstance :=
  (i.1, i.2, 2)

open Classical in
/-- GRAPH THICKNESS 2 as a decision problem over bitstrings. -/
noncomputable def graphThicknessTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphThicknessTwoInstance) x with
  | some i => decide (GraphThickness.WellFormed (withBound i) ∧
      GraphThickness.GraphThicknessFeasible (withBound i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphThicknessTwo
