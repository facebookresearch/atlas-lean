/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on planar bipartite graphs of maximum degree 3 and girth at least 9 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 190, problem [GT2] DOMINATING SET,
comment: "Remains NP-complete for planar graphs with maximum vertex degree 3" [Garey and
Johnson, unpublished];
I. E. Zverovich and V. E. Zverovich, "An induced subgraph characterization of domination
perfect graphs", Journal of Graph Theory 20 (1995), 375-395, doi:10.1002/jgt.3190200313;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1226`
(bipartite ∩ girth >= 9 ∩ maximum degree 3 ∩ planar), problem Domination: NP-complete
(Zverovich and Zverovich 1995).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import WantedExt.Complexity.NPComplete.DominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetPlanarBipartiteSubcubicGirthNine

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on planar bipartite graphs of maximum degree 3 and girth at least 9

INSTANCE: a graph `G = (V, E)` that is planar, bipartite, of maximum degree at most `3`, and of
girth at least `9` (no cycle of length less than `9`), and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex of `V - V'` is adjacent to a vertex of `V'`?

This is DOMINATING SET on the ISGCI class `gc_1226`, bipartite ∩ girth >= 9 ∩ maximum degree 3
∩ planar. The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.DominatingSetWanted` ([GT2]: a simple graph on `Fin n` given by
an edge list, and the bound `K`). The restriction adds `0 < K ≤ |V|` ([GT2]'s instance class)
and the class: planarity as the repository's `SimpleGraph.IsPlanar` (a crossing-free
straight-line drawing, `MathlibExt.Combinatorics.SimpleGraph.Planarity`), bipartiteness as
Mathlib's `SimpleGraph.IsBipartite`, the degree bound as Mathlib's `SimpleGraph.degree`, and
the girth bound with Mathlib's extended girth `SimpleGraph.egirth` (the length of a shortest
cycle, `⊤` for a forest).

Garey and Johnson record DOMINATING SET as NP-complete on planar graphs of maximum degree `3`.
Replacing every edge by a path with three inner vertices keeps the graph planar and the degrees
of the original vertices, adds inner vertices of degree `2`, multiplies every cycle length by
`4` (so the graph becomes bipartite of girth at least `12`), and raises the domination number by
exactly the number of edges; this reduces that problem to the one stated here. ISGCI records
the NP-completeness of this class with the citation Zverovich and Zverovich (1995).

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
whose graph is planar, bipartite, of maximum degree at most `3` and of girth at least `9`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ (Graph i).IsPlanar ∧
    (Graph i).IsBipartite ∧ (∀ v, (Graph i).degree v ≤ 3) ∧ 9 ≤ (Graph i).egirth

open Classical in
/-- DOMINATING SET on planar bipartite graphs of maximum degree 3 and girth at least 9, as a
decision problem over bitstrings. -/
noncomputable def dominatingSetPlanarBipartiteSubcubicGirthNineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET on planar bipartite graphs of maximum degree 3 and girth at least 9 is
NP-complete.** Source: Garey and Johnson (1979), [GT2], comment, with edge subdivision;
Zverovich and Zverovich (1995); ISGCI (`gc_1226`). -/
public theorem_wanted dominatingSetPlanarBipartiteSubcubicGirthNine_npComplete :
    dominatingSetPlanarBipartiteSubcubicGirthNineDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetPlanarBipartiteSubcubicGirthNineDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetPlanarBipartiteSubcubicGirthNine
