/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR 4-REGULAR GRAPH 3-COLORABILITY: definitions

Source:
D. P. Dailey, "Uniqueness of colorability and colorability of planar 4-regular graphs are
NP-complete", Discrete Mathematics 30(3) (1980), 289-293, doi:10.1016/0012-365X(80)90236-8.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PlanarDegreeFourThreeColorabilityDefs
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarFourRegularThreeColorability

open PlanarDegreeFourThreeColorability
  (PlanarDegreeFourThreeColorabilityInstance Graph PlanarDegreeFourThreeColorabilityFeasible)

open Classical in
/-- Well-formedness of an instance: well formed for PLANAR GRAPH 3-COLORABILITY (maximum degree
4), so a simple planar graph, and every vertex has degree exactly 4. -/
def WellFormed (i : PlanarDegreeFourThreeColorabilityInstance) : Prop :=
  PlanarDegreeFourThreeColorability.WellFormed i ∧ (Graph i).IsRegularOfDegree 4

open Classical in
/-- PLANAR 4-REGULAR GRAPH 3-COLORABILITY as a decision problem over bitstrings. -/
noncomputable def planarFourRegularThreeColorabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarDegreeFourThreeColorabilityInstance) x with
  | some i => decide (WellFormed i ∧ PlanarDegreeFourThreeColorabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarFourRegularThreeColorability
