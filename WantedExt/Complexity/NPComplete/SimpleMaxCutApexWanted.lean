/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on apex graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] SIMPLE MAX CUT;
ISGCI (https://www.graphclasses.org/classes/gc_1181.html), class "apex", problem "Maximum cut"
(decision variant): NP-complete, with the references M. Kamiński, "max-cut and containment
relations in graphs", WG 2010, Lecture Notes in Computer Science 6410 (2010), 15-26,
doi:10.1007/978-3-642-16926-7_4 (journal version: Theoretical Computer Science 438 (2012),
89-95, doi:10.1016/j.tcs.2012.02.036), and F. Barahona, "The max-cut problem on graphs not
contractible to K₅", Operations Research Letters 2 (1983), 107-111,
doi:10.1016/0167-6377(83)90016-0.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import WantedExt.Complexity.NPComplete.MaxCutWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutApex

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT on apex graphs is NP-complete

INSTANCE: an apex graph `G = (V, E)`, that is, a graph with a vertex `v` such that `G - v` is
planar, and a positive integer `K`.
QUESTION: is there a partition of `V` into disjoint sets `V₁` and `V₂` such that at least `K`
edges of `E` have one endpoint in `V₁` and one endpoint in `V₂`?

ISGCI records the decision variant of maximum cut ("the vertices of G can be partitioned into
two sets A,B such that there are at least k edges in G with one endpoint in A and the other
endpoint in B") as NP-complete on apex graphs, citing Kamiński (2010) and Barahona (1983). On
planar graphs the problem is polynomial (Hadlock 1975), and Barahona's polynomial algorithm
covers graphs not contractible to `K₅`; apex graphs are the next step.

This is the restriction of SIMPLE MAX CUT ([ND16]; MAXIMUM CUT with unit weights,
`WantedExt.Complexity.NPComplete.MaxCutWanted`, whose question already counts edges) to apex
graphs, with `K` positive as in [ND16]. The instance, the simple-edge-list conditions and the
question are those of that module, reused here, as in
`WantedExt.Complexity.NPComplete.SimpleMaxCutDegreeThreeWanted`. `G - v` is the subgraph
induced on the other vertices (`SimpleGraph.induce`), and planarity is the shared MathlibExt
predicate `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, equivalent to planarity
by Fáry's theorem). Apex graphs are recognized in polynomial time (a planarity test for each
choice of `v`), so the restriction does not affect membership in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `G` is an apex graph: deleting some vertex `v` leaves a planar graph. -/
def IsApex {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ v : V, (G.induce {w | w ≠ v}).IsPlanar

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, …, n - 1`) whose graph is an apex graph, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧ IsApex (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧ 0 < i.2.2

/-- A partition `V₁ = S`, `V₂ = V - S` with at least `K` edges between the two sets (the
MAXIMUM CUT question). -/
def SimpleMaxCutApexFeasible (i : MaxCutInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- SIMPLE MAX CUT on apex graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutApexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ SimpleMaxCutApexFeasible i)
  | none => false

/-- **SIMPLE MAX CUT on apex graphs is NP-complete.** Source: Garey and Johnson (1979), [ND16];
ISGCI gc_1181 (Kamiński 2010; Barahona 1983). -/
public theorem_wanted simpleMaxCutApex_npComplete :
    simpleMaxCutApexDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutApexDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutApex
