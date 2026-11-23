/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF GRAPHS OF DIAMETER AT MOST 3 is NP-complete

Source:
G. B. Mertzios and P. G. Spirakis, "Algorithms and almost tight results for 3-colorability of
small diameter graphs", Algorithmica 74(1) (2016), 385-414, doi:10.1007/s00453-014-9949-6
(Theorem 6: 3-coloring is NP-complete on triangle-free graphs with diameter 3 and radius 2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted
public import Mathlib.Combinatorics.SimpleGraph.Diam

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityDiameterThree

open GraphColoring (GraphColoringInstance Graph GraphColoringFeasible)

/-!
# 3-COLORABILITY OF GRAPHS OF DIAMETER AT MOST 3 is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)`, with at least one vertex, of diameter at
most 3. QUESTION: is `G` properly 3-colorable?

This is GRAPH COLORING (`GraphColoringWanted`) with the bound fixed to `K = 3`, restricted to
graphs of diameter at most 3. The diameter is Mathlib's `SimpleGraph.ediam`, the supremum of the
path distances `d(u, v)`, as in the source (`diam(G) = max {d(u, v) : u, v ∈ V}`); it is `⊤`
for a disconnected graph, so the graphs of the instance class are connected. The source's
maximum over vertex pairs needs a vertex, and Mathlib's `ediam` of the graph on `Fin 0` is `0`,
so `WellFormed` asks for `n ≥ 1`. Mertzios and
Spirakis (Theorem 6) prove 3-coloring NP-complete already on triangle-free graphs of diameter
exactly 3 and radius 2, a subclass of the instance class here; membership in NP holds for all
graphs.

The instance type is a vertex count and an edge list; `withThreeColors` pairs it with the bound
`3` to reuse GRAPH COLORING's graph (`Graph`, a simple graph on `Fin n`), well-formedness
(simple edge list) and question (`Colorable 3`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev ThreeColorabilityDiameterThreeInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH COLORING instance with the same graph and bound `K = 3`. -/
abbrev withThreeColors (i : ThreeColorabilityDiameterThreeInstance) : GraphColoringInstance :=
  (i.1, i.2, 3)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (GRAPH
COLORING's well-formedness), the graph has at least one vertex, and it has diameter at most 3. -/
def WellFormed (i : ThreeColorabilityDiameterThreeInstance) : Prop :=
  GraphColoring.WellFormed (withThreeColors i) ∧ 0 < i.1 ∧
    (Graph (withThreeColors i)).ediam ≤ 3

/-- The graph is properly 3-colorable. -/
def ThreeColorabilityDiameterThreeFeasible (i : ThreeColorabilityDiameterThreeInstance) : Prop :=
  GraphColoringFeasible (withThreeColors i)

open Classical in
/-- 3-COLORABILITY OF GRAPHS OF DIAMETER AT MOST 3 as a decision problem over bitstrings. -/
noncomputable def threeColorabilityDiameterThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeColorabilityDiameterThreeInstance) x with
  | some i => decide (WellFormed i ∧ ThreeColorabilityDiameterThreeFeasible i)
  | none => false

/-- **3-COLORABILITY OF GRAPHS OF DIAMETER AT MOST 3 is NP-complete.** Source: Mertzios and
Spirakis (2016), Theorem 6. -/
public theorem_wanted threeColorabilityDiameterThree_npComplete :
    threeColorabilityDiameterThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityDiameterThreeDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityDiameterThree
