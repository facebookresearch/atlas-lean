/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET for 2P₃-free graphs is NP-complete

Source:
I. E. Zverovich, "Satgraphs and independent domination. Part 1", Theoretical Computer Science
352(1-3) (2006), 47-56, doi:10.1016/j.tcs.2005.08.038;
ISGCI, Information System on Graph Classes and their Inclusions, class 2P₃-free (gc_931,
https://www.graphclasses.org/classes/gc_931.html), problem Independent dominating set;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IndependentDominatingSetTwoP3FreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetTwoP3Free

/-!
# INDEPENDENT DOMINATING SET for 2P₃-free graphs is NP-complete

INSTANCE: a 2P₃-free graph `G = (V, E)`, that is, a graph with no induced subgraph isomorphic to
`2P₃`, the disjoint union of two paths on three vertices, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain a set `S` of pairwise non-adjacent vertices with `|S| ≤ K` such that
every vertex of `G` is in `S` or adjacent to a vertex of `S`?

This is the restriction of INDEPENDENT DOMINATING SET (`IndependentDominatingSetWanted`) to
2P₃-free graphs. The instance type, the graph and the question are the parent's
(`IndependentDominatingSet.IndependentDominatingSetInstance`, `IndependentDominatingSet.Graph`,
`IndependentDominatingSet.IndependentDominatingSetFeasible`); `WellFormed` is the parent's plus
the restriction and the dominating-set bounds `0 < K ≤ |V|` of Garey and Johnson's [GT2].
"`X`-free" is Mathlib's `SimpleGraph.IsIndContained` (an induced embedding), negated, as in the
other forbidden-subgraph restrictions in this directory; `2P₃` is
`SimpleGraph.pathGraph 3 ⊕g SimpleGraph.pathGraph 3` (Mathlib's path graph and disjoint sum),
ISGCI's small graph `2P₃` (graph6 `EgCG`, edges `01, 12, 34, 45`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDEPENDENT DOMINATING SET for 2P₃-free graphs is NP-complete.** Source: Zverovich (2006);
ISGCI (gc_931). -/
public theorem_wanted independentDominatingSetTwoP3Free_npComplete :
    independentDominatingSetTwoP3FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentDominatingSetTwoP3FreeDec

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetTwoP3Free
