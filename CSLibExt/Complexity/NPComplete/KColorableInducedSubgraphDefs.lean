/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-COLORABLE INDUCED SUBGRAPH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT21] INDUCED SUBGRAPH
WITH PROPERTY Π (comment);
J. M. Lewis and M. Yannakakis, "The node-deletion problem for hereditary properties is
NP-complete", Journal of Computer and System Sciences 20 (1980), 219-230,
doi:10.1016/0022-0000(80)90060-4;
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MAXIMUM K-COLORABLE INDUCED SUBGRAPH.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import CSLibExt.Complexity.NPComplete.InducedSubgraphWithPropertyPiDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KColorableInducedSubgraph

/-- The graph property "`k`-colorable": a graph on `Fin m` has a coloring with at most `k`
colors (`SimpleGraph.Colorable k`). -/
def colorableProperty (k : ℕ) : InducedSubgraphWithPropertyPi.GraphProperty :=
  fun _ G => G.Colorable k

/-- K-COLORABLE INDUCED SUBGRAPH, for a fixed `k`, as a decision problem over bitstrings:
INDUCED SUBGRAPH WITH PROPERTY Π for `Π` = `k`-colorable. -/
noncomputable def kColorableInducedSubgraphDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  InducedSubgraphWithPropertyPi.inducedSubgraphWithPropertyPiDec (colorableProperty k)

end MetaMathlibExt.Complexity.NPComplete.KColorableInducedSubgraph
