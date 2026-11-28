/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY of circle graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY
(CHROMATIC NUMBER), p. 191 (comment: "For arbitrary `K`, the problem is NP-complete for circle
graphs and circular arc graphs (even given their representation as families of arcs)");
M. R. Garey, D. S. Johnson, G. L. Miller and C. H. Papadimitriou, "The complexity of coloring
circular arcs and chords", SIAM Journal on Algebraic and Discrete Methods 1 (1980), 216-227,
doi:10.1137/0601025.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import CSLibExt.Complexity.NPComplete.DominatingSetCircleGraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringCircleGraph

open MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph (circleGraph)

/-- An instance: the chords, one per vertex, each given by its endpoints `(a, b)`, and the
number of colors `K`. -/
abbrev GraphColoringCircleGraphInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every chord has endpoints `a < b`, all endpoints of all
chords are distinct, and `0 < K ≤ |V|`. -/
def WellFormed (i : GraphColoringCircleGraphInstance) : Prop :=
  (∀ c ∈ i.1, c.1 < c.2) ∧ (i.1.flatMap fun c => [c.1, c.2]).Nodup ∧ 0 < i.2 ∧ i.2 ≤ i.1.length

/-- The circle graph of the chords has a proper coloring with at most `K` colors. -/
def GraphColoringCircleGraphFeasible (i : GraphColoringCircleGraphInstance) : Prop :=
  (circleGraph i.1).Colorable i.2

open Classical in
/-- GRAPH K-COLORABILITY of circle graphs as a decision problem over bitstrings. -/
noncomputable def graphColoringCircleGraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringCircleGraphInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoringCircleGraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphColoringCircleGraph
