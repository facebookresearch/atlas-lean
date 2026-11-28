/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED PLANAR SUBGRAPH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT27] PLANAR SUBGRAPH, p. 197
(comment: "Corresponding problem in which `G'` is the subgraph induced by a set `V'` of at
least `K` vertices is also NP-complete");
M. S. Krishnamoorthy and N. Deo, "Node-deletion NP-complete problems", SIAM Journal on
Computing 8 (1979), 619-625, doi:10.1137/0208049 (property (v), planar);
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.InducedSubgraphWithPropertyPiDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedPlanarSubgraph

/-- The graph property "planar": a graph on `Fin m` has a crossing-free straight-line drawing
(`SimpleGraph.IsPlanar`). -/
def planarProperty : InducedSubgraphWithPropertyPi.GraphProperty :=
  fun _ G => G.IsPlanar

/-- INDUCED PLANAR SUBGRAPH as a decision problem over bitstrings: INDUCED SUBGRAPH WITH
PROPERTY Π for `Π` = planar. -/
noncomputable def inducedPlanarSubgraphDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  InducedSubgraphWithPropertyPi.inducedSubgraphWithPropertyPiDec planarProperty

end MetaMathlibExt.Complexity.NPComplete.InducedPlanarSubgraph
