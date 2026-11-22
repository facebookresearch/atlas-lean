/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR 4-REGULAR GRAPH 3-COLORABILITY is NP-complete

Source:
D. P. Dailey, "Uniqueness of colorability and colorability of planar 4-regular graphs are
NP-complete", Discrete Mathematics 30(3) (1980), 289-293, doi:10.1016/0012-365X(80)90236-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PlanarDegreeFourThreeColorabilityWanted
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarFourRegularThreeColorability

open PlanarDegreeFourThreeColorability
  (PlanarDegreeFourThreeColorabilityInstance Graph PlanarDegreeFourThreeColorabilityFeasible)

/-!
# PLANAR 4-REGULAR GRAPH 3-COLORABILITY is NP-complete

An instance is a planar graph `G = (V, E)` in which every vertex has degree exactly 4. The
question is whether `G` is 3-colorable. This is the restriction of PLANAR GRAPH 3-COLORABILITY
(maximum degree 4), `PlanarDegreeFourThreeColorabilityWanted`, to 4-regular graphs; Dailey
(1980) proves it NP-complete.

The instance type, the graph (`Graph`, a simple graph on `Fin n` given by an edge list), the
parent's well-formedness (simple edge list, planarity as MathlibExt's `SimpleGraph.IsPlanar`,
degrees at most 4) and the question (`Colorable 3`) are reused from
`PlanarDegreeFourThreeColorabilityWanted`; only 4-regularity, Mathlib's
`SimpleGraph.IsRegularOfDegree 4`, is added to the well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PLANAR 4-REGULAR GRAPH 3-COLORABILITY is NP-complete.** Source: Dailey (1980). -/
public theorem_wanted planarFourRegularThreeColorability_npComplete :
    planarFourRegularThreeColorabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarFourRegularThreeColorabilityDec

end MetaMathlibExt.Complexity.NPComplete.PlanarFourRegularThreeColorability
