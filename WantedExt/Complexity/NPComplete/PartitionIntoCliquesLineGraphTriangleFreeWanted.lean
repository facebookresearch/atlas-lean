/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on line graphs of triangle-free graphs is NP-complete

Source:
A. Munaro, "Bounded clique cover of some sparse graphs", Discrete Mathematics 340(9) (2017),
2208-2216, doi:10.1016/j.disc.2017.04.004;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES and problem [GT1]
VERTEX COVER;
ISGCI (https://www.graphclasses.org/classes/gc_708.html), problem "Clique cover" on line graphs of
triangle-free graphs: NP-complete, with the attribution to Munaro (2017).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import WantedExt.Complexity.NPComplete.PartitionIntoCliquesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLineGraphTriangleFree

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph WellFormed
  PartitionIntoCliquesFeasible)

/-!
# PARTITION INTO CLIQUES on line graphs of triangle-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is the line graph of a triangle-free graph, and a positive
integer `K ≤ |V|`. QUESTION: can the vertices of `G` be partitioned into `k ≤ K` sets each of
which induces a complete graph?

`G` is the line graph of a triangle-free graph (ISGCI class `gc_708`) when `G ≅ L(H)` for some
graph `H` without a triangle, where Mathlib's `SimpleGraph.lineGraph` has the edges of `H` as
vertices, two distinct edges adjacent when they share an endpoint. The existential over a root on
`Fin k` has the shape of `MetaMathlibExt.SimpleGraph.IsLineGraph`, with the root's
triangle-freeness (Mathlib's `CliqueFree 3`) added. Line graphs and their roots are recognized in
polynomial time, so the restriction keeps the problem in NP.

The instance, its graph, its well-formedness (a simple edge list and `0 < K ≤ |V|`) and the
question are those of PARTITION INTO CLIQUES (`PartitionIntoCliquesWanted`, Garey and Johnson's
[GT15]); this module adds the class restriction to well-formedness. ISGCI records the problem as
NP-complete on this class, citing Munaro (2017). In a triangle-free root every clique of `L(H)`
is a set of edges with a common endpoint, so `L(H)` splits into `K` cliques exactly when `H` has a
vertex cover of size at most `K`, and VERTEX COVER ([GT1]) stays NP-complete on triangle-free
graphs (Poljak 1974, by subdividing every edge twice).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `G` is the line graph of a triangle-free graph: `G ≅ L(H)` for a graph `H` on `Fin k`
without a triangle. -/
def IsLineGraphOfTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (H : SimpleGraph (Fin k)), H.CliqueFree 3 ∧ Nonempty (G ≃g H.lineGraph)

/-- Well-formedness of an instance: a well-formed PARTITION INTO CLIQUES instance whose graph is
the line graph of a triangle-free graph. -/
def LineGraphWellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  WellFormed i ∧ IsLineGraphOfTriangleFree (Graph i)

open Classical in
/-- PARTITION INTO CLIQUES on line graphs of triangle-free graphs as a decision problem over
bitstrings. -/
noncomputable def partitionIntoCliquesLineGraphTriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PartitionIntoCliquesInstance) x with
  | some i => decide (LineGraphWellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

/-- **PARTITION INTO CLIQUES on line graphs of triangle-free graphs is NP-complete.** Source:
Munaro (2017); Garey and Johnson (1979), [GT15]; ISGCI, class `gc_708`. -/
public theorem_wanted partitionIntoCliquesLineGraphTriangleFree_npComplete :
    partitionIntoCliquesLineGraphTriangleFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesLineGraphTriangleFreeDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesLineGraphTriangleFree
