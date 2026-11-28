/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY of circle graphs for fixed K ≥ 4: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
W. Unger, "On the k-colouring of circle-graphs", STACS 88, Lecture Notes in Computer Science
294 (1988), 61-72, doi:10.1007/BFb0035832;
P. Bachmann, I. Rutter and P. Stumpf, "On 3-coloring circle graphs", Journal of Graph
Algorithms and Applications 28 (2024), 389-402, doi:10.7155/jgaa.v28i1.2991.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import CSLibExt.Complexity.NPComplete.DominatingSetCircleGraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircleGraphFixedKColoring

open MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph (circleGraph)

/-- An instance: the chords, one per vertex, each given by its endpoints `(a, b)`; the number
of colors `K` is fixed. -/
abbrev CircleGraphFixedKColoringInstance := List (ℕ × ℕ)

/-- Well-formedness of an instance: every chord has endpoints `a < b`, and all endpoints of all
chords are distinct. -/
def WellFormed (i : CircleGraphFixedKColoringInstance) : Prop :=
  (∀ c ∈ i, c.1 < c.2) ∧ (i.flatMap fun c => [c.1, c.2]).Nodup

/-- The circle graph of the chords has a proper coloring with at most `K` colors. -/
def CircleGraphFixedKColoringFeasible (K : ℕ) (i : CircleGraphFixedKColoringInstance) : Prop :=
  (circleGraph i).Colorable K

open Classical in
/-- GRAPH K-COLORABILITY of circle graphs for a fixed `K` as a decision problem over
bitstrings. -/
noncomputable def circleGraphFixedKColoringDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CircleGraphFixedKColoringInstance) x with
  | some i => decide (WellFormed i ∧ CircleGraphFixedKColoringFeasible K i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CircleGraphFixedKColoring
