/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on 2-DIR graphs is NP-complete

Source:
J. Kratochvíl and J. Nešetřil, "INDEPENDENT SET and CLIQUE problems in intersection-defined
classes of graphs", Commentationes Mathematicae Universitatis Carolinae 31(1) (1990), 85-93,
http://dml.cz/dmlcz/106821 (Theorem 1: "INDEPENDENT SET is polynomially solvable in 1-DIR and
PURE-2-DIR, but it is NP-complete when restricted to 2-DIR and PURE-3-DIR");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET (the parent problem);
ISGCI (https://www.graphclasses.org/classes/gc_864.html), class "2-DIR", problem "Independent
set": NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted
public import WantedExt.Complexity.NPComplete.TwoDirRecognitionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoDir

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-!
# INDEPENDENT SET on 2-DIR graphs is NP-complete

INSTANCE: a 2-DIR graph `G = (V, E)`, i.e. the intersection graph of straight line segments lying
in at most 2 directions in the plane, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) on the ISGCI class `gc_864`, with Kratochvíl and Nešetřil's
definition of 2-DIR. The class is `TwoDirRecognition.IsTwoDir` from
`WantedExt.Complexity.NPComplete.TwoDirRecognitionWanted` (one non-degenerate horizontal or
vertical segment with integer endpoints per vertex, two distinct vertices adjacent exactly when
their segments share a point; that module explains why these representations give exactly the
2-DIR graphs). The instance type (vertex count `n`, edge list, bound `K`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (a `Finset` of at least `K`
vertices whose coercion is Mathlib's `SimpleGraph.IsIndepSet`) are those of the edge-list
INDEPENDENT SET statement `WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`,
whose triangle-free restriction lives only in its `WellFormed`, which this module does not use.
`WellFormed` here asks for the simple edge list of `TwoDirRecognition.WellFormed`, the class, and
`0 < K ≤ |V|` ([GT20]'s instance class).

Kratochvíl and Nešetřil's reduction maps a planar graph of maximum degree 4 to a subdivision
together with a 2-DIR representation of it, so the problem is NP-hard with the graph given
without its representation. It is in NP: the vertices incident to no edge (all but at most
twice the length of the edge list) lie in every maximum independent set and need no listing, so
a certificate is a 2-DIR representation as in `TwoDirRecognitionWanted` together with an
independent set of the remaining vertices.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`
(`TwoDirRecognition.WellFormed`), the graph is a 2-DIR graph, and `0 < K ≤ n`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  TwoDirRecognition.WellFormed (i.1, i.2.1) ∧ TwoDirRecognition.IsTwoDir (Graph i) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on 2-DIR graphs as a decision problem over bitstrings. -/
noncomputable def independentSetTwoDirDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

/-- **INDEPENDENT SET on 2-DIR graphs is NP-complete.** Source: Kratochvíl and Nešetřil (1990),
Theorem 1; ISGCI (`gc_864`); Garey and Johnson (1979), [GT20] (parent problem). -/
public theorem_wanted independentSetTwoDir_npComplete :
    independentSetTwoDirDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetTwoDirDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoDir
