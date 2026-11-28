/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX CUT on unit disk graphs: definitions

Source:
J. Díaz and M. Kamiński, "MAX-CUT and MAX-BISECTION are NP-hard on unit disk graphs",
Theoretical Computer Science 377 (2007), 271-276, doi:10.1016/j.tcs.2007.02.013 (preprint
arXiv:cs/0609128).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs
public import CSLibExt.Complexity.NPComplete.UnitDiskDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCutUnitDiskGraphs

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutFeasible)
open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (RatCode)
open MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet (unitDiskGraph)

/-- An instance: the disk centers (pairs of rational coordinates), the edge list of the graph,
and the bound `K`. -/
abbrev MaxCutUnitDiskGraphsInstance := List (RatCode × RatCode) × List (ℕ × ℕ) × ℕ

/-- The MAXIMUM CUT instance `(|P|, E, K)` of the graph. -/
def toMaxCut (i : MaxCutUnitDiskGraphsInstance) : MaxCut.MaxCutInstance :=
  (i.1.length, i.2.1, i.2.2)

/-- Well-formedness of an instance: positive denominators; distinct centers; a well-formed
MAXIMUM CUT instance on the vertices `0, ..., |P| - 1`; the edge list is the unit disk graph of
the centers; and `0 < K`. -/
def WellFormed (i : MaxCutUnitDiskGraphsInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p.1.2 ∧ 0 < p.2.2) ∧ (i.1.map fun p => (p.1.val, p.2.val)).Nodup ∧
    MaxCut.WellFormed (toMaxCut i) ∧
    Cslib.Complexity.Karp.edgeGraph i.1.length i.2.1 = unitDiskGraph i.1 ∧ 0 < i.2.2

/-- A partition of the vertices with at least `K` edges between the two sets (the MAXIMUM CUT
question on `(|P|, E, K)`). -/
def MaxCutUnitDiskGraphsFeasible (i : MaxCutUnitDiskGraphsInstance) : Prop :=
  MaxCutFeasible (toMaxCut i)

open Classical in
/-- MAX CUT on unit disk graphs as a decision problem over bitstrings. -/
noncomputable def maxCutUnitDiskGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutUnitDiskGraphsInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutUnitDiskGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaxCutUnitDiskGraphs
