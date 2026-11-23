/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for planar graphs of maximum degree 3 is NP-complete

Source:
B. Monien and I. H. Sudborough, "Min cut is NP-complete for edge weighted trees", Theoretical
Computer Science 58(1-3) (1988), 209-229, doi:10.1016/0304-3975(88)90028-X (abstract: "derive
from this the NP-completeness of Min Cut for planar graphs with maximum vertex degree 3");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementPlanarMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement
  (MinimumCutLinearArrangementInstance MinimumCutLinearArrangementFeasible)

/-!
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for planar graphs of maximum degree 3 is NP-complete

INSTANCE: a planar graph `G = (V, E)` with no vertex degree exceeding `3`, and a positive
integer `K`.
QUESTION: is the cutwidth of `G` at most `K`, i.e. is there a one-to-one function
`f : V → {1, 2, ..., |V|}` such that for all `i`, `1 ≤ i < |V|`,
`|{{u, v} ∈ E : f(u) ≤ i < f(v)}| ≤ K`?

This is the restriction of MINIMUM CUT LINEAR ARRANGEMENT ([GT44],
`MinimumCutLinearArrangementWanted`) to planar graphs of maximum degree `3`. The instance type
and the question are the parent's
(`MinimumCutLinearArrangement.MinimumCutLinearArrangementInstance`,
`MinimumCutLinearArrangement.MinimumCutLinearArrangementFeasible`), and `WellFormed` is the
parent's (a simple edge list on `0, ..., n - 1` and `0 < K`) plus the restriction, on the
instance's graph `Cslib.Complexity.Karp.edgeGraph`: planarity is MathlibExt's
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's theorem exists
exactly for planar graphs), and the degree bound uses Mathlib's `SimpleGraph.degree`.

Membership in NP: the certificate is the arrangement; degrees are checked directly and planarity
in linear time (Hopcroft and Tarjan, J. ACM 21 (1974), 549-568).

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
/-- Well-formedness of an instance: the parent's (the edge list describes a simple graph on
`0, ..., n - 1`, and `0 < K`), and the graph is planar with every vertex degree at most `3`. -/
def WellFormed (i : MinimumCutLinearArrangementInstance) : Prop :=
  MinimumCutLinearArrangement.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsPlanar ∧
      ∀ v, (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).degree v ≤ 3

open Classical in
/-- MINIMUM CUT LINEAR ARRANGEMENT for planar graphs of maximum degree 3 as a decision problem
over bitstrings. -/
noncomputable def minimumCutLinearArrangementPlanarMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutLinearArrangementInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCutLinearArrangementFeasible i)
  | none => false

/-- **MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for planar graphs of maximum degree 3 is
NP-complete.** Source: Monien and Sudborough (1988); Garey and Johnson (1979), [GT44]. -/
public theorem_wanted minimumCutLinearArrangementPlanarMaxDegreeThree_npComplete :
    minimumCutLinearArrangementPlanarMaxDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCutLinearArrangementPlanarMaxDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementPlanarMaxDegreeThree
