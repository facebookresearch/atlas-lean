/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for chordal graphs is NP-complete

Source:
K. S. Booth and J. H. Johnson, "Dominating sets in chordal graphs", SIAM Journal on Computing
11(1) (1982), 191-199, doi:10.1137/0211015;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DominatingSetChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetChordalGraphs

/-!
# DOMINATING SET for chordal graphs is NP-complete

INSTANCE: a chordal graph `G = (V, E)`, that is, a graph in which every cycle of length at least
`4` has a chord, and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex not in `V'` is joined to at least one member of `V'`?

This is the restriction of DOMINATING SET ([GT2], `DominatingSetDefs`) to chordal graphs. The
instance type, the graph and the question are the parent's (`DominatingSet.DominatingSetInstance`,
`DominatingSet.Graph`, `DominatingSet.DominatingSetFeasible`); `WellFormed` is the parent's plus
the restriction and Garey and Johnson's bounds `0 < K ≤ |V|`. Chordality is stated as in
`PathwidthChordalGraphsWanted`: no cycle graph `Cₖ` with `k ≥ 4` is an induced subgraph
(Mathlib's `SimpleGraph.cycleGraph` and `SimpleGraph.IsIndContained`; a cycle has a chord exactly
when its vertices do not induce a cycle graph).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DOMINATING SET for chordal graphs is NP-complete.** Source: Booth and Johnson (1982);
Garey and Johnson (1979), [GT2]. -/
public theorem_wanted dominatingSetChordalGraphs_npComplete :
    dominatingSetChordalGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetChordalGraphsDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetChordalGraphs
