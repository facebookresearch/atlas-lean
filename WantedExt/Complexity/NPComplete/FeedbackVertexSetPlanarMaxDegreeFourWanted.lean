/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on planar graphs of maximum degree 4 is NP-complete

Source:
E. Speckenmeyer, "On feedback vertex sets and nonseparating independent sets in cubic graphs",
Journal of Graph Theory 12(3) (1988), 405-412, doi:10.1002/jgt.3190120311;
T. Bai, Y. Cao and M. Xiao, "Feedback set problems on bounded-degree (planar) graphs",
arXiv:2605.11407 (2026), Section 1 (records that Speckenmeyer, and independently two other
groups, settled the undirected problem on planar graphs of maximum degree four in the 1980s);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (undirected version in
the comment);
ISGCI (https://www.graphclasses.org/classes/gc_909.html), problem "Feedback vertex set" on planar
graphs of maximum degree 4: NP-complete, with the attribution to Speckenmeyer (1988).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPlanarMaxDegreeFour

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

/-!
# FEEDBACK VERTEX SET on planar graphs of maximum degree 4 is NP-complete

INSTANCE: a planar graph `G = (V, E)` in which every vertex has degree at most `4`, and a
bound `K` (as in the parent module). QUESTION: is there a set `S ⊆ V` of at most `K` vertices
such that `G - S` is a forest?

Planarity is the repository's `SimpleGraph.IsPlanar` (`MathlibExt`: a crossing-free
straight-line drawing, which by Fáry's theorem exists exactly for planar graphs); the degree
bound uses Mathlib's `SimpleGraph.degree` (ISGCI class `gc_909`: planar, and every vertex has
degree at most 4). The instance, its graph, its well-formedness (a simple edge list) and the
question (`G - S` acyclic for some `|S| ≤ K`) are those of FEEDBACK VERTEX SET
(`FeedbackVertexSetWanted`); this module adds the class restriction to well-formedness. The
problem is polynomial for maximum degree `3` (Ueno, Kajitani and Gotoh 1988), so the bound `4`
is where hardness starts. Planarity and degrees are checked in polynomial time, so the
restricted problem is in NP.

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
/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance whose graph is
planar with every degree at most `4`. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ (Graph i).IsPlanar ∧ ∀ v, (Graph i).degree v ≤ 4

open Classical in
/-- FEEDBACK VERTEX SET on planar graphs of maximum degree 4 as a decision problem over
bitstrings. -/
noncomputable def feedbackVertexSetPlanarMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

/-- **FEEDBACK VERTEX SET on planar graphs of maximum degree 4 is NP-complete.** Source:
Speckenmeyer (1988); Bai, Cao and Xiao (2026), Section 1; ISGCI, class `gc_909`. -/
public theorem_wanted feedbackVertexSetPlanarMaxDegreeFour_npComplete :
    feedbackVertexSetPlanarMaxDegreeFourDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetPlanarMaxDegreeFourDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPlanarMaxDegreeFour
