/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on domination perfect triangle-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 190, problem [GT2] DOMINATING SET,
comment: "Remains NP-complete for planar graphs with maximum vertex degree 3" [Garey and
Johnson, unpublished];
I. E. Zverovich and V. E. Zverovich, "An induced subgraph characterization of domination
perfect graphs", Journal of Graph Theory 20 (1995), 375-395, doi:10.1002/jgt.3190200313
(definition of domination perfect graphs; NP-completeness of DOMINATING SET on classes of them);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_553`
(domination perfect ∩ triangle-free), problem Domination: NP-complete (Zverovich and Zverovich
1995; and on its subclass `gc_529`, Zverovich and Zverovich 2006).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import WantedExt.Complexity.NPComplete.DominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetDominationPerfectTriangleFree

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on domination perfect triangle-free graphs is NP-complete

INSTANCE: a triangle-free graph `G = (V, E)` that is domination perfect, i.e. `γ(H) = i(H)` for
every induced subgraph `H` of `G`, where `γ` is the domination number and `i` the independent
domination number, and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex of `V - V'` is adjacent to a vertex of `V'`?

This is DOMINATING SET on the ISGCI class `gc_553`, domination perfect ∩ triangle-free. The
instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.DominatingSetWanted` ([GT2]: a simple graph on `Fin n` given by
an edge list, and the bound `K`). The restriction adds `0 < K ≤ |V|` ([GT2]'s instance class),
triangle-freeness as Mathlib's `SimpleGraph.CliqueFree 3`, and domination perfectness with the
repository's `SimpleGraph.dominationNumber` and `SimpleGraph.indepDominationNumber`
(`MathlibExt.Combinatorics.SimpleGraph.Domination`), over the subgraphs `G.induce U` induced by
the vertex sets `U` (the empty graph included, where both numbers are `0`).

Garey and Johnson record DOMINATING SET as NP-complete on planar graphs of maximum degree `3`.
Replacing every edge by a path with three inner vertices raises the domination number by exactly
the number of edges, and the resulting graphs, and all their induced subgraphs, are
triangle-free with no two adjacent vertices of degree at least `3`; in such a graph `γ = i`.
(Take a minimum dominating set with the fewest edges inside it. An end of an inside edge has
only outside private neighbours; if it had just one, exchanging the two would give a minimum
dominating set with fewer inside edges. So both ends would have two private neighbours and
degree at least `3`.) ISGCI records the NP-completeness of this class with the citation
Zverovich and Zverovich (1995).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A graph on `Fin n` is domination perfect: every induced subgraph has equal domination
number and independent domination number (Zverovich and Zverovich 1995). -/
def IsDominationPerfect {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ U : Finset (Fin n),
    (G.induce (U : Set (Fin n))).dominationNumber =
      (G.induce (U : Set (Fin n))).indepDominationNumber

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K ≤ |V|`
whose graph is triangle-free and domination perfect. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ (Graph i).CliqueFree 3 ∧
    IsDominationPerfect (Graph i)

open Classical in
/-- DOMINATING SET on domination perfect triangle-free graphs as a decision problem over
bitstrings. -/
noncomputable def dominatingSetDominationPerfectTriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET on domination perfect triangle-free graphs is NP-complete.** Source: Garey
and Johnson (1979), [GT2], comment, with edge subdivision; Zverovich and Zverovich (1995); ISGCI
(`gc_553`). -/
public theorem_wanted dominatingSetDominationPerfectTriangleFree_npComplete :
    dominatingSetDominationPerfectTriangleFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetDominationPerfectTriangleFreeDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetDominationPerfectTriangleFree
