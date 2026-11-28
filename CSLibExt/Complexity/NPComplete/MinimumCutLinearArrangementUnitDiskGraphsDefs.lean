/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) on unit disk graphs: definitions

Source:
J. Díaz, M. D. Penrose, J. Petit and M. Serna, "Linear orderings of random geometric graphs
(extended abstract)", in *Graph-Theoretic Concepts in Computer Science (WG 1999)*, Lecture Notes
in Computer Science 1665, Springer (1999), 291-302, doi:10.1007/3-540-46784-X_28 (Theorem 1:
"Bandwidth, MinCut and VertSep remain NP-complete even when restricted to grid graphs (and
therefore, even when restricted to unit disk graphs)"); journal version: "Approximating layout
problems on random geometric graphs", Journal of Algorithms 39 (2001), 78-116,
doi:10.1006/jagm.2000.1149;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT (the
parent problem).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumCutLinearArrangementDefs
public import CSLibExt.Complexity.NPComplete.UnitDiskDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementUnitDiskGraphs

open MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement
  (MinimumCutLinearArrangementInstance MinimumCutLinearArrangementFeasible)
open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (RatCode)
open MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet (unitDiskGraph)

/-- An instance: the disk centers (pairs of rational coordinates), the edge list of the graph,
and the bound `K`. -/
abbrev MinimumCutLinearArrangementUnitDiskGraphsInstance :=
  List (RatCode × RatCode) × List (ℕ × ℕ) × ℕ

/-- The MINIMUM CUT LINEAR ARRANGEMENT instance `(|P|, E, K)` of the graph. -/
def toMinimumCutLinearArrangement (i : MinimumCutLinearArrangementUnitDiskGraphsInstance) :
    MinimumCutLinearArrangementInstance :=
  (i.1.length, i.2.1, i.2.2)

/-- Well-formedness of an instance: positive denominators; distinct centers; a well-formed
MINIMUM CUT LINEAR ARRANGEMENT instance on the vertices `0, ..., |P| - 1`; and the edge list is
the unit disk graph of the centers. -/
def WellFormed (i : MinimumCutLinearArrangementUnitDiskGraphsInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p.1.2 ∧ 0 < p.2.2) ∧ (i.1.map fun p => (p.1.val, p.2.val)).Nodup ∧
    MinimumCutLinearArrangement.WellFormed (toMinimumCutLinearArrangement i) ∧
    Cslib.Complexity.Karp.edgeGraph i.1.length i.2.1 = unitDiskGraph i.1

/-- The MINIMUM CUT LINEAR ARRANGEMENT question on `(|P|, E, K)` for the supplied edge list
`E`, which counts its entries; for a well-formed instance, `E` is the simple edge list of the unit
disk graph and this says its cutwidth is at most `K`. -/
def MinimumCutLinearArrangementUnitDiskGraphsFeasible
    (i : MinimumCutLinearArrangementUnitDiskGraphsInstance) : Prop :=
  MinimumCutLinearArrangementFeasible (toMinimumCutLinearArrangement i)

open Classical in
/-- MINIMUM CUT LINEAR ARRANGEMENT on unit disk graphs as a decision problem over bitstrings. -/
noncomputable def minimumCutLinearArrangementUnitDiskGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutLinearArrangementUnitDiskGraphsInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCutLinearArrangementUnitDiskGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementUnitDiskGraphs
