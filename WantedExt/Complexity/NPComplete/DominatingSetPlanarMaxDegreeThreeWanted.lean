/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on planar graphs of maximum degree 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET, p. 190, comment:
"Remains NP-complete for planar graphs with maximum vertex degree 3" (credited there to
[Garey and Johnson, unpublished]);
I. E. Zverovich and V. E. Zverovich, "An induced subgraph characterization of domination
perfect graphs", Journal of Graph Theory 20 (1995), 375-395, doi:10.1002/jgt.3190200313
(NP-completeness on planar bipartite graphs of maximum degree 3 and girth at least 9, a
subclass, as recorded by ISGCI for class `gc_1226`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetPlanarMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on planar graphs of maximum degree 3 is NP-complete

INSTANCE: a planar graph `G = (V, E)` with maximum vertex degree at most `3`, and a positive
integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e., a subset `V' ⊆ V` with
`|V'| ≤ K` such that for all `u ∈ V - V'` there is a `v ∈ V'` for which `{u, v} ∈ E`?

The instance, its graph, the simple-edge-list well-formedness and the question are those of
`CSLibExt.Complexity.NPComplete.DominatingSetDefs` ([GT2]). The restriction adds
`0 < K ≤ |V|` ([GT2]'s instance class) and the class: planarity as the repository's
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's theorem exists
exactly for planar graphs) and the degree bound as Mathlib's `SimpleGraph.degree`.

Membership in NP: the certificate is `V'`; degrees are checked directly and planarity in linear
time (Hopcroft and Tarjan, J. ACM 21 (1974), 549-568). Hardness: Garey and Johnson record the
result (unpublished proof); the published reduction of Zverovich and Zverovich outputs planar
bipartite graphs of maximum degree `3` (girth at least `9`), which are instances of this
problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K ≤ |V|`
whose graph is planar with every vertex degree at most `3`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ (Graph i).IsPlanar ∧
    ∀ v, (Graph i).degree v ≤ 3

open Classical in
/-- DOMINATING SET on planar graphs of maximum degree 3 as a decision problem over
bitstrings. -/
noncomputable def dominatingSetPlanarMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET on planar graphs of maximum degree 3 is NP-complete.** Source: Garey and
Johnson (1979), [GT2], comment; Zverovich and Zverovich (1995). -/
public theorem_wanted dominatingSetPlanarMaxDegreeThree_npComplete :
    dominatingSetPlanarMaxDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetPlanarMaxDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetPlanarMaxDegreeThree
