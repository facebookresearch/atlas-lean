/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX CUT on split graphs is NP-complete

Source:
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Nordic Journal of
Computing 7(1) (2000), 14-31 (conference version: STACS 94, LNCS 775 (1994), 769-780,
doi:10.1007/3-540-57785-8_189).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaxCutSplitGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCutSplitGraphs

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)
open MetaMathlibExt.Complexity.NPComplete.DominatingSetSplitGraphs (IsSplitGraph)

/-!
# MAX CUT on split graphs is NP-complete

INSTANCE: a split graph `G = (V, E)`, i.e. a graph whose vertex set can be partitioned into a
clique and an independent set, and a positive integer `K`. QUESTION: is there a partition of `V`
into disjoint sets `V₁` and `V₂` such that at least `K` edges of `E` have one endpoint in `V₁`
and one endpoint in `V₂`? This is SIMPLE MAX CUT restricted to split graphs; Bodlaender and
Jansen show it NP-complete for split graphs (hence for chordal graphs).

The instance, the simple-edge-list conditions, and the question are those of MAXIMUM CUT
(`CSLibExt.Complexity.NPComplete.MaxCutDefs`, whose question counts edges), reused here as
in `SimpleMaxCutDegreeThreeWanted`. The restriction is the repository's split-graph predicate
`DominatingSetSplitGraphs.IsSplitGraph` (from `DominatingSetSplitGraphsWanted`: some finite set of
vertices is a clique and its complement an independent set, with Mathlib's
`SimpleGraph.IsClique` and `SimpleGraph.IsIndepSet`; either part may be empty) applied to
`Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAX CUT on split graphs is NP-complete.** Source: Bodlaender and Jansen (2000). -/
public theorem_wanted maxCutSplitGraphs_npComplete :
    maxCutSplitGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxCutSplitGraphsDec

end MetaMathlibExt.Complexity.NPComplete.MaxCutSplitGraphs
