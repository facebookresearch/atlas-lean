/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 5-COLORABILITY OF P6-FREE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
S. Huang, "Improved complexity results on k-coloring P_t-free graphs", European Journal of
Combinatorics 51 (2016), 336-346, doi:10.1016/j.ejc.2015.06.005.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiveColorabilityP6Free

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# 5-COLORABILITY OF P6-FREE GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` with no induced path on 6 vertices.
QUESTION: is `G` properly 5-colorable?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`) with `K = 5`, restricted to
`P_6`-free graphs. A graph is `P_6`-free when it has no induced subgraph isomorphic to the
path `P_6` on 6 vertices: Mathlib's `(SimpleGraph.pathGraph 6).IsIndContained G` (an induced
embedding of `P_6` into `G`) fails. Huang proves that 4-COLORING is NP-complete for
`P_7`-free graphs and 5-COLORING is NP-complete for `P_6`-free graphs.

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and bound `K`, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable K`). The
restriction adds `K = 5` and `P_6`-freeness to well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `K = 5`
whose graph is `P_6`-free (has no induced path on 6 vertices). -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 5 ∧
    ¬ (SimpleGraph.pathGraph 6).IsIndContained (Graph i)

open Classical in
/-- 5-COLORABILITY OF P6-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def fiveColorabilityP6FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **5-COLORABILITY OF P6-FREE GRAPHS is NP-complete.** Source: Garey and Johnson (1979), [GT4];
Huang (2016). -/
public theorem_wanted fiveColorabilityP6Free_npComplete :
    fiveColorabilityP6FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L fiveColorabilityP6FreeDec

end MetaMathlibExt.Complexity.NPComplete.FiveColorabilityP6Free
