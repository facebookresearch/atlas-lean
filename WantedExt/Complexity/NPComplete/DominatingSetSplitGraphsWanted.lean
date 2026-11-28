/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for split graphs is NP-complete

Source:
A. A. Bertossi, "Dominating sets for split and bipartite graphs", Information Processing
Letters 19(1) (1984), 37-40, doi:10.1016/0020-0190(84)90126-1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DominatingSetSplitGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetSplitGraphs

/-!
# DOMINATING SET for split graphs is NP-complete

INSTANCE: a split graph `G = (V, E)`, that is, a graph whose vertex set can be partitioned into
a clique and an independent set, and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex not in `V'` is joined to at least one member of `V'`?

This is the restriction of DOMINATING SET ([GT2], `DominatingSetDefs`) to split graphs. The
instance type, the graph and the question are the parent's (`DominatingSet.DominatingSetInstance`,
`DominatingSet.Graph`, `DominatingSet.DominatingSetFeasible`); `WellFormed` is the parent's plus
the restriction and Garey and Johnson's bounds `0 < K ≤ |V|`. The clique and the independent
set use Mathlib's `SimpleGraph.IsClique` and `SimpleGraph.IsIndepSet`; either part may be empty.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DOMINATING SET for split graphs is NP-complete.** Source: Bertossi (1984); Garey and
Johnson (1979), [GT2]. -/
public theorem_wanted dominatingSetSplitGraphs_npComplete :
    dominatingSetSplitGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetSplitGraphsDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetSplitGraphs
