/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET IN UNIT DISK GRAPHS is NP-complete

Source:
B. N. Clark, C. J. Colbourn and D. S. Johnson, "Unit disk graphs", Discrete Mathematics
86(1-3) (1990), 165-177, doi:10.1016/0012-365X(90)90358-O;
A. Tkachenko and H. Wang, "Dominating set, independent set, discrete k-center, dispersion, and
related problems for planar points in convex position", arXiv:2501.00207 (2024), Section 1
(definition of the unit-disk graph of a point set; NP-hardness of independent set on unit-disk
graphs, credited to Clark, Colbourn and Johnson);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitDiskDominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitDiskIndependentSet

open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (RatCode)
open MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet (unitDiskGraph)

/-!
# INDEPENDENT SET IN UNIT DISK GRAPHS is NP-complete

INSTANCE: a finite set `P` of points in the plane with rational coordinates, given explicitly,
and a positive integer `K ≤ |P|`. The unit disk graph of `P` has vertex set `P` and joins two
points at (Euclidean) distance at most `1`.
QUESTION: is there a set of at least `K` points of `P`, no two at distance at most `1`, that is,
an independent set of size at least `K` in the unit disk graph?

Points and the unit disk graph are those of
`WantedExt.Complexity.NPComplete.UnitDiskDominatingSetWanted` (`unitDiskGraph`: rational points
placed in `EuclideanSpace ℝ (Fin 2)`, adjacent when their Euclidean `dist` is at most `1`).
`P` is a set, so the points are distinct. Independence is Mathlib's `SimpleGraph.IsIndepSet`.
The bound `K ≤ |P|` follows the instance class of [GT20] INDEPENDENT SET; for `K > |P|` the
answer is trivially no.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the points of `P` (pairs of rational coordinates) and the bound `K`. -/
abbrev UnitDiskIndependentSetInstance := List (RatCode × RatCode) × ℕ

/-- Well-formedness of an instance: all denominators are positive, the points are distinct (as
points of the plane), and `1 ≤ K ≤ |P|`. -/
def WellFormed (i : UnitDiskIndependentSetInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p.1.2 ∧ 0 < p.2.2) ∧ (i.1.map fun p => (p.1.val, p.2.val)).Nodup ∧
    1 ≤ i.2 ∧ i.2 ≤ i.1.length

/-- The unit disk graph of `P` has an independent set of at least `K` points. -/
def UnitDiskIndependentSetFeasible (i : UnitDiskIndependentSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1.length), i.2 ≤ S.card ∧ (unitDiskGraph i.1).IsIndepSet ↑S

open Classical in
/-- INDEPENDENT SET IN UNIT DISK GRAPHS as a decision problem over bitstrings. -/
noncomputable def unitDiskIndependentSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitDiskIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ UnitDiskIndependentSetFeasible i)
  | none => false

/-- **INDEPENDENT SET IN UNIT DISK GRAPHS is NP-complete.** Source: Clark, Colbourn and Johnson
(1990). -/
public theorem_wanted unitDiskIndependentSet_npComplete :
    unitDiskIndependentSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitDiskIndependentSetDec

end MetaMathlibExt.Complexity.NPComplete.UnitDiskIndependentSet
