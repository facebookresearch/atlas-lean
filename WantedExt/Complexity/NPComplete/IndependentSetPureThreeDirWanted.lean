/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on PURE-3-DIR graphs is NP-complete

Source:
J. Kratochvíl and J. Nešetřil, "INDEPENDENT SET and CLIQUE problems in intersection-defined
classes of graphs", Commentationes Mathematicae Universitatis Carolinae 31(1) (1990), 85-93,
http://dml.cz/dmlcz/106821 (Theorem 1);
J. Kratochvíl and J. Matoušek, "Intersection graphs of segments", Journal of Combinatorial
Theory, Series B 62 (1994), 289-315, doi:10.1006/jctb.1994.1071 (recognition of PURE-k-DIR is
in NP);
ISGCI, *Information System on Graph Classes and their Inclusions*, class PURE-3-DIR (gc_868),
problem Independent set: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PureKDirGraphRecognitionWanted
public import WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetPureThreeDir

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)
open PureKDirGraphRecognition (IsPureKDirGraph)

/-!
# INDEPENDENT SET on PURE-3-DIR graphs is NP-complete

INSTANCE: a PURE-3-DIR graph `G = (V, E)`, that is, the intersection graph of straight line
segments lying in at most 3 directions in the plane such that any two parallel segments are
disjoint, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

Kratochvíl and Nešetřil (1990), Theorem 1: "INDEPENDENT SET is polynomially solvable in 1-DIR
and PURE-2-DIR, but it is NP-complete when restricted to 2-DIR and PURE-3-DIR". Their reduction,
from INDEPENDENT SET on planar graphs of maximum degree four, constructs a PURE-3-DIR segment
representation, so its output graphs lie in the class. The instance here is the graph, as in
ISGCI's problem on class gc_868, and membership in the class is part of `WellFormed`; the
language is in NP because an independent set is a certificate and recognizing PURE-`k`-DIR
graphs is in NP for every fixed `k` (Kratochvíl and Matoušek, 1994). The segment-input version
of INDEPENDENT SET on all segment intersection graphs is `IndependentSetSegmentIntersectionWanted`.

The instance type (vertex count `n`, edge list, bound `K`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (a `Finset` of at least `K`
vertices whose coercion is Mathlib's `SimpleGraph.IsIndepSet`) are those of
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`, whose triangle-free
restriction lives only in its `WellFormed`, which this module does not use. `WellFormed` here
asks for a simple edge list on `Fin n`, `0 < K ≤ |V|` ([GT20]'s instance class), and that the
graph is PURE-3-DIR: `PureKDirGraphRecognition.IsPureKDirGraph 3`, the representation of
`PureKDirGraphRecognitionWanted` (closed non-vertical segments whose slopes lie among 3 reals,
segments of equal slope pairwise disjoint, two distinct vertices adjacent exactly when their
segments meet).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) that is a PURE-3-DIR
graph, and `0 < K ≤ |V|`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    IsPureKDirGraph 3 (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on PURE-3-DIR graphs as a decision problem over bitstrings. -/
noncomputable def independentSetPureThreeDirDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

/-- **INDEPENDENT SET on PURE-3-DIR graphs is NP-complete.** Source: Kratochvíl and Nešetřil
(1990), Theorem 1; Kratochvíl and Matoušek (1994); ISGCI (gc_868). -/
public theorem_wanted independentSetPureThreeDir_npComplete :
    independentSetPureThreeDirDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetPureThreeDirDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetPureThreeDir
