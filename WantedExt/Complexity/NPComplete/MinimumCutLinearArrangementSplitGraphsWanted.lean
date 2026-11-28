/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for split graphs is NP-complete

Source:
P. Heggernes, D. Lokshtanov, R. Mihai and C. Papadopoulos, "Cutwidth of split graphs, threshold
graphs, and proper interval graphs", in *Graph-Theoretic Concepts in Computer Science (WG 2008)*,
Lecture Notes in Computer Science 5344, Springer (2008), 218-229,
doi:10.1007/978-3-540-92248-3_20;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumCutLinearArrangementSplitGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementSplitGraphs

open MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement
  (MinimumCutLinearArrangementInstance MinimumCutLinearArrangementFeasible)

/-!
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for split graphs is NP-complete

INSTANCE: a split graph `G = (V, E)`, that is, a graph whose vertex set can be partitioned into
a clique and an independent set, and a positive integer `K`.
QUESTION: is the cutwidth of `G` at most `K`, i.e. is there a one-to-one function
`f : V → {1, 2, ..., |V|}` such that for all `i`, `1 ≤ i < |V|`,
`|{{u, v} ∈ E : f(u) ≤ i < f(v)}| ≤ K`?

This is the restriction of MINIMUM CUT LINEAR ARRANGEMENT ([GT44],
`MinimumCutLinearArrangementWanted`) to split graphs. The instance type and the question are the
parent's (`MinimumCutLinearArrangement.MinimumCutLinearArrangementInstance`,
`MinimumCutLinearArrangement.MinimumCutLinearArrangementFeasible`), and `WellFormed` is the
parent's (a simple edge list on `0, ..., n - 1` and `0 < K`) plus the restriction. Split graphs
are the repository's `DominatingSetSplitGraphs.IsSplitGraph` (a clique `C`, Mathlib's
`SimpleGraph.IsClique`, whose complement is an independent set, `SimpleGraph.IsIndepSet`; either
part may be empty), applied to the instance's graph `Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for split graphs is NP-complete.** Source:
Heggernes, Lokshtanov, Mihai and Papadopoulos (2008); Garey and Johnson (1979), [GT44]. -/
public theorem_wanted minimumCutLinearArrangementSplitGraphs_npComplete :
    minimumCutLinearArrangementSplitGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCutLinearArrangementSplitGraphsDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementSplitGraphs
