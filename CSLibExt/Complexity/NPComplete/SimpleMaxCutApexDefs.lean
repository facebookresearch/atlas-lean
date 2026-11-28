/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on apex graphs: definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutApex

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutApex
