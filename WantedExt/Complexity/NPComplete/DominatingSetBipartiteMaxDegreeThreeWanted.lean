/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on bipartite graphs of maximum degree 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 190, problem [GT2] DOMINATING SET,
comment: "Remains NP-complete for planar graphs with maximum vertex degree 3" [Garey and
Johnson, unpublished];
I. E. Zverovich and V. E. Zverovich, "An induced subgraph characterization of domination
perfect graphs", Journal of Graph Theory 20 (1995), 375-395, doi:10.1002/jgt.3190200313;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_941`
(bipartite ∩ maximum degree 3, https://www.graphclasses.org/classes/gc_941.html), problem
Domination: NP-complete, from the subclass bipartite ∩ girth >= 9 ∩ maximum degree 3 ∩ planar
(Zverovich and Zverovich 1995).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import WantedExt.Complexity.NPComplete.DominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetBipartiteMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on bipartite graphs of maximum degree 3 is NP-complete

INSTANCE: a graph `G = (V, E)` that is bipartite and of maximum degree at most `3`, and a
positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex of `V - V'` is adjacent to a vertex of `V'`?

This is DOMINATING SET on the ISGCI class `gc_941`, bipartite ∩ maximum degree 3. The instance,
its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.DominatingSetWanted` ([GT2]: a simple graph on `Fin n` given by
an edge list, and the bound `K`). The restriction adds `0 < K ≤ |V|` ([GT2]'s instance class)
and the class: bipartiteness as Mathlib's `SimpleGraph.IsBipartite` and the degree bound as
Mathlib's `SimpleGraph.degree`.

Every planar bipartite graph of maximum degree `3` and girth at least `9` is an instance, and
DOMINATING SET is NP-complete on that subclass
(`WantedExt.Complexity.NPComplete.DominatingSetPlanarBipartiteSubcubicGirthNineWanted`: Garey
and Johnson's planar maximum degree `3` case with every edge subdivided; ISGCI cites Zverovich
and Zverovich 1995); ISGCI derives the NP-completeness of `gc_941` from that subclass. Both
class conditions are checked in polynomial time, so the problem is in NP.

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
whose graph is bipartite and of maximum degree at most `3`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ (Graph i).IsBipartite ∧
    ∀ v, (Graph i).degree v ≤ 3

open Classical in
/-- DOMINATING SET on bipartite graphs of maximum degree 3 as a decision problem over
bitstrings. -/
noncomputable def dominatingSetBipartiteMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET on bipartite graphs of maximum degree 3 is NP-complete.** Source: Garey
and Johnson (1979), [GT2], comment; Zverovich and Zverovich (1995); ISGCI (`gc_941`). -/
public theorem_wanted dominatingSetBipartiteMaxDegreeThree_npComplete :
    dominatingSetBipartiteMaxDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetBipartiteMaxDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetBipartiteMaxDegreeThree
