/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET on planar bipartite subcubic graphs of girth at least 9 is NP-complete

Source:
I. E. Zverovich and V. E. Zverovich, "An induced subgraph characterization of domination
perfect graphs", Journal of Graph Theory 20(3) (1995), 375-395, doi:10.1002/jgt.3190200313;
ISGCI, Information System on Graph Classes and their Inclusions, class bipartite ∩ girth >= 9 ∩
maximum degree 3 ∩ planar (gc_1226, https://www.graphclasses.org/classes/gc_1226.html), problem
Independent dominating set;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), p. 190, problem [GT2] DOMINATING SET, comment: "Also
NP-complete if V' is required to be both a dominating set and an independent set."
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IndependentDominatingSetPlanarBipartiteSubcubicGirthNineDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetPlanarBipartiteSubcubicGirthNine

/-!
# INDEPENDENT DOMINATING SET on planar bipartite subcubic graphs of girth at least 9 is NP-complete

INSTANCE: a graph `G = (V, E)` that is planar, bipartite, of maximum degree at most `3`, and of
girth at least `9` (no cycle of length less than `9`), and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain a set `S` of pairwise non-adjacent vertices with `|S| ≤ K` such that
every vertex of `G` is in `S` or adjacent to a vertex of `S`?

This is the restriction of INDEPENDENT DOMINATING SET (`IndependentDominatingSetWanted`) to the
ISGCI class gc_1226, bipartite ∩ girth >= 9 ∩ maximum degree 3 ∩ planar. The instance type, the
graph and the question are the parent's
(`IndependentDominatingSet.IndependentDominatingSetInstance`,
`IndependentDominatingSet.Graph`, `IndependentDominatingSet.IndependentDominatingSetFeasible`).
The instance class is exactly the one of the DOMINATING SET restriction to the same graph class,
so `WellFormed` is `DominatingSetPlanarBipartiteSubcubicGirthNine.WellFormed`: the edge list is
simple (`DominatingSet.WellFormed`, the same condition as `IndependentDominatingSet.WellFormed`),
`0 < K ≤ |V|` ([GT2]'s instance class), and the graph `edgeGraph n edges` (both parents' `Graph`)
is planar (the repository's `SimpleGraph.IsPlanar`), bipartite (Mathlib's
`SimpleGraph.IsBipartite`), of degree at most `3` (`SimpleGraph.degree`), and of extended girth
at least `9` (Mathlib's `SimpleGraph.egirth`, `⊤` for a forest).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDEPENDENT DOMINATING SET on planar bipartite subcubic graphs of girth at least 9 is
NP-complete.** Source: Zverovich and Zverovich (1995);
ISGCI (gc_1226); Garey and Johnson (1979), [GT2]. -/
public theorem_wanted independentDominatingSetPlanarBipartiteSubcubicGirthNine_npComplete :
    independentDominatingSetPlanarBipartiteSubcubicGirthNineDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L
            independentDominatingSetPlanarBipartiteSubcubicGirthNineDec

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetPlanarBipartiteSubcubicGirthNine
