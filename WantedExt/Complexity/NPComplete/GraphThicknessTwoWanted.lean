/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH THICKNESS 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN3];
A. Mansfield, "Determining the thickness of graphs is NP-hard", Mathematical Proceedings of the
Cambridge Philosophical Society 93 (1983), 9-23, doi:10.1017/S030500410006028X.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphThicknessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphThicknessTwo

/-!
# GRAPH THICKNESS 2 is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: does `G` have thickness two or less, i.e., can `E` be
partitioned into two sets `E₁, E₂` such that each subgraph `Gᵢ = (V, Eᵢ)` is planar? Mansfield
proves this NP-complete, answering Garey and Johnson's open problem.

This is GRAPH THICKNESS (`WantedExt.Complexity.NPComplete.GraphThicknessWanted`) with the bound
fixed at `K = 2` instead of being part of the instance: the question and the well-formedness
conditions are that module's, applied to the instance `(n, E, 2)` (`withBound`). Planarity is
the shared MathlibExt predicate `SimpleGraph.IsPlanar` used there.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **GRAPH THICKNESS 2 is NP-complete.** Source: Garey and Johnson (1979), [OPEN3];
Mansfield (1983). -/
public theorem_wanted graphThicknessTwo_npComplete :
    graphThicknessTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphThicknessTwoDec

end MetaMathlibExt.Complexity.NPComplete.GraphThicknessTwo
