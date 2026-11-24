/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on 2-subdivision ∩ planar graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), pp. 191-192, problem [GT7] FEEDBACK VERTEX
SET, comment: "The corresponding problem for undirected graphs is also NP-complete";
E. Speckenmeyer, "On feedback vertex sets and nonseparating independent sets in cubic graphs",
Journal of Graph Theory 12(3) (1988), 405-412, doi:10.1002/jgt.3190120311 (as cited by
`FeedbackVertexSetPlanarMaxDegreeFourWanted`: NP-complete on planar graphs of maximum degree 4);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_675`
(2-subdivision ∩ planar, https://www.graphclasses.org/classes/gc_675.html), problem Feedback
vertex set: NP-complete, with its note 1648 (communicated by P. Irzhavsky): the 2-subdivision of
a graph has a feedback vertex set of size `k` iff the graph does, and the reduction maintains
planarity.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted
public import WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementTwoSubdivisionPlanarWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTwoSubdivisionPlanar

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)
open MinimumCutLinearArrangementTwoSubdivisionPlanar (IsTwoSubdivision)

/-!
# FEEDBACK VERTEX SET on 2-subdivision ∩ planar graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is planar and a 2-subdivision, and a positive integer
`K ≤ |V|`. A
2-subdivision of a graph `H` results from inserting two new vertices in every edge, that is,
from replacing each edge `uv` of `H` by a path `u x y v` with new vertices `x, y`; `G` is a
2-subdivision if it is the 2-subdivision of some graph (ISGCI's class 2-subdivision ∩ planar,
`gc_675`).
QUESTION: is there a set `S ⊆ V` of at most `K` vertices such that every cycle of `G` contains
a vertex of `S`, i.e. `G - S` is a forest?

The instance, its graph, its well-formedness (a simple edge list) and the question (`G - S`
acyclic for some `|S| ≤ K`) are those of FEEDBACK VERTEX SET
(`WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted`). `WellFormed` adds `0 < K ≤ |V|`
([GT7]'s instance class) and the class, with the predicates of
`WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementTwoSubdivisionPlanarWanted`:
planarity is MathlibExt's `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by
Fáry's theorem this is planarity), and `IsTwoSubdivision G` says that `G` is isomorphic to the
2-subdivision of a simple graph given by a simple edge list.

ISGCI's note 1648 gives the reduction from FEEDBACK VERTEX SET on planar graphs, which is
NP-complete (Speckenmeyer 1988, even for maximum degree 4): a feedback vertex set of `H` is one
of its 2-subdivision, and a vertex of a feedback vertex set of the 2-subdivision that is not a
vertex of `H` can be replaced by its neighbour in `H`, so the 2-subdivision has a feedback
vertex set of size `k` iff `H` does; subdividing edges preserves planarity. The problem is in
NP: a certificate gives `H` (at most `|V|` vertices and `|E| / 3` edges), the isomorphism and
the set `S`, and planarity is decided in polynomial time (by Fáry's theorem, `IsPlanar` is
planarity).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance with
`0 < K ≤ |V|` whose graph is a 2-subdivision and planar. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ IsTwoSubdivision (Graph i) ∧
    (Graph i).IsPlanar

open Classical in
/-- FEEDBACK VERTEX SET on 2-subdivision ∩ planar graphs as a decision problem over
bitstrings. -/
noncomputable def feedbackVertexSetTwoSubdivisionPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

/-- **FEEDBACK VERTEX SET on 2-subdivision ∩ planar graphs is NP-complete.** Source: Garey and
Johnson (1979), [GT7], comment; Speckenmeyer (1988); ISGCI (`gc_675`, note 1648). -/
public theorem_wanted feedbackVertexSetTwoSubdivisionPlanar_npComplete :
    feedbackVertexSetTwoSubdivisionPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetTwoSubdivisionPlanarDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTwoSubdivisionPlanar
