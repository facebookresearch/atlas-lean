/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on planar graphs is NP-complete

Source:
A. Munaro, "On line graphs of subcubic triangle-free graphs", Discrete Mathematics 340(6)
(2017), 1210-1226, doi:10.1016/j.disc.2017.01.006, introduction ("Feedback Vertex Set becomes
NP-hard for graphs with maximum degree 4, even if restricted to be planar, as shown by
Speckenmeyer", citing the two works below);
E. Speckenmeyer, *Untersuchungen zum Feedback Vertex Set Problem in ungerichteten Graphen*,
Ph.D. thesis, Universität Paderborn (1983) (not available here);
E. Speckenmeyer, "On feedback vertex sets and nonseparating independent sets in cubic graphs",
Journal of Graph Theory 12(3) (1988), 405-412, doi:10.1002/jgt.3190120311;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (comment: "The
corresponding problem for undirected graphs is also NP-complete");
ISGCI (https://www.graphclasses.org/classes/gc_43.html), class "planar", problem "Feedback
vertex set": NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPlanar

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

/-!
# FEEDBACK VERTEX SET on planar graphs is NP-complete

INSTANCE: a planar graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is there a set
`S ⊆ V` of at most `K` vertices such that every cycle of `G` contains a vertex of `S`, i.e.
`G - S` is a forest?

Planarity is the repository's `SimpleGraph.IsPlanar` (`MathlibExt`: a crossing-free
straight-line drawing, which by Fáry's theorem exists exactly for planar graphs; ISGCI class
`gc_43`). The instance, its graph, its well-formedness (a simple edge list) and the question
(`G - S` acyclic for some `|S| ≤ K`) are those of FEEDBACK VERTEX SET
(`FeedbackVertexSetWanted`); this module adds planarity and the bound `0 < K ≤ |V|` of
Garey and Johnson's [GT7] instance to well-formedness.

Speckenmeyer proved the problem NP-complete already on planar graphs of maximum degree `4` (the
restriction stated in `FeedbackVertexSetPlanarMaxDegreeFourWanted`), a subclass of the planar
graphs, so the problem on planar graphs is NP-hard. Planarity is checked in polynomial time and
the deleted set is a certificate, so the problem is in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET on planar graphs is NP-complete.** Source: Speckenmeyer (1983, 1988),
via planar graphs of maximum degree 4, as recorded by Munaro (2017); ISGCI, class `gc_43`. -/
public theorem_wanted feedbackVertexSetPlanar_npComplete :
    feedbackVertexSetPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetPlanarDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPlanar
