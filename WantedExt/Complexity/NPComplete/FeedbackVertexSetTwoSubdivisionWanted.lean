/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on 2-subdivision graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), pp. 191-192, problem [GT7] FEEDBACK VERTEX
SET, comment: "The corresponding problem for undirected graphs is also NP-complete";
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_472`
(2-subdivision, https://www.graphclasses.org/classes/gc_472.html), problem Feedback vertex set:
NP-complete, with its note 1648 (communicated by P. Irzhavsky): the 2-subdivision of a graph
has a feedback vertex set of size `k` iff the graph does.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetTwoSubdivisionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTwoSubdivision

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)
open MinimumCutLinearArrangementTwoSubdivisionPlanar (IsTwoSubdivision)

/-!
# FEEDBACK VERTEX SET on 2-subdivision graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is a 2-subdivision, and a positive integer `K ≤ |V|`. A
2-subdivision of a graph `H` results from inserting two new vertices in every edge, that is,
from replacing each edge `uv` of `H` by a path `u x y v` with new vertices `x, y`; `G` is a
2-subdivision if it is the 2-subdivision of some graph (ISGCI's class 2-subdivision).
QUESTION: is there a set `S ⊆ V` of at most `K` vertices such that every cycle of `G` contains
a vertex of `S`, i.e. `G - S` is a forest?

The instance, its graph, its well-formedness (a simple edge list) and the question (`G - S`
acyclic for some `|S| ≤ K`) are those of FEEDBACK VERTEX SET
(`WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted`). `WellFormed` adds `0 < K ≤ |V|`
([GT7]'s instance class) and the class, with the predicate `IsTwoSubdivision` of
`WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementTwoSubdivisionPlanarWanted`: `G` is
isomorphic to the 2-subdivision of a simple graph given by a simple edge list.

ISGCI's note 1648 gives the reduction from FEEDBACK VERTEX SET, which is NP-complete for
undirected graphs ([GT7], comment): a feedback vertex set of `H` is one of its 2-subdivision,
and a vertex of a feedback vertex set of the 2-subdivision that is not a vertex of `H` can be
replaced by its neighbour in `H`, so the 2-subdivision has a feedback vertex set of size `k`
iff `H` does. The problem is in NP: a certificate gives `H` (at most `|V|` vertices and
`|E| / 3` edges), the isomorphism, and the set `S`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET on 2-subdivision graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT7], comment; ISGCI (`gc_472`, note 1648). -/
public theorem_wanted feedbackVertexSetTwoSubdivision_npComplete :
    feedbackVertexSetTwoSubdivisionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetTwoSubdivisionDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTwoSubdivision
