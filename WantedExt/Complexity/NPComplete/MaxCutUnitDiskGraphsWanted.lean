/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX CUT on unit disk graphs is NP-complete

Source:
J. Díaz and M. Kamiński, "MAX-CUT and MAX-BISECTION are NP-hard on unit disk graphs",
Theoretical Computer Science 377 (2007), 271-276, doi:10.1016/j.tcs.2007.02.013 (preprint
arXiv:cs/0609128).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MaxCutWanted
public import WantedExt.Complexity.NPComplete.UnitDiskDominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCutUnitDiskGraphs

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutFeasible)
open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (RatCode)
open MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet (unitDiskGraph)

/-!
# MAX CUT on unit disk graphs is NP-complete

INSTANCE: a unit disk graph `G` given with an intersection model, i.e. distinct points of the
plane (the centers of disks of diameter one) such that two vertices are adjacent exactly when
their disks intersect, which happens exactly when the centers are at distance at most `1`; and
a positive integer `K`. QUESTION: is there a partition of the vertices into two sets with at
least `K` edges between them? Díaz and Kamiński prove MAX-CUT NP-hard on unit disk graphs;
membership in NP is immediate (the partition is the certificate).

Points have rational coordinates in the encoding of `PlanarKMeansWanted` (`RatCode`), and the
graph of the model is the repository's `UnitDiskDominatingSet.unitDiskGraph` (distinct points at
Euclidean distance at most `1` are adjacent). The instance lists the points, the edges of `G`,
and `K`: well-formedness requires positive denominators, distinct centers ("the centers of disks
do not coincide"), a MAXIMUM CUT edge list on the vertices `0, ..., |P| - 1`, and that this edge
list is exactly the unit disk graph of the points. The question is MAXIMUM CUT's
(`WantedExt.Complexity.NPComplete.MaxCutWanted`) on `(|P|, E, K)`, reused unchanged.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MAX CUT on unit disk graphs is NP-complete.** Source: Díaz and Kamiński (2007). -/
public theorem_wanted maxCutUnitDiskGraphs_npComplete :
    maxCutUnitDiskGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxCutUnitDiskGraphsDec

end MetaMathlibExt.Complexity.NPComplete.MaxCutUnitDiskGraphs
