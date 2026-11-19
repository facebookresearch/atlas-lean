/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET IN UNIT DISK GRAPHS is NP-complete

Source:
B. N. Clark, C. J. Colbourn and D. S. Johnson, "Unit disk graphs", Discrete Mathematics
86(1-3) (1990), 165-177, doi:10.1016/0012-365X(90)90358-O;
A. Tkachenko and H. Wang, "Dominating set, independent set, discrete k-center, dispersion, and
related problems for planar points in convex position", arXiv:2501.00207 (2024), Section 1
(definition of the unit-disk graph of a point set; NP-hardness of dominating set on unit-disk
graphs, credited to Clark, Colbourn and Johnson);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import WantedExt.Complexity.NPComplete.PlanarKMeansWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet

open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (RatCode point)

/-!
# DOMINATING SET IN UNIT DISK GRAPHS is NP-complete

INSTANCE: a finite set `P` of points in the plane with rational coordinates, given explicitly,
and a positive integer `K ≤ |P|`. The unit disk graph of `P` has vertex set `P` and joins two
points at (Euclidean) distance at most `1`.
QUESTION: is there a dominating set of at most `K` points in the unit disk graph, that is, a set
`D ⊆ P` with `|D| ≤ K` such that every point of `P` is in `D` or at distance at most `1` from a
point of `D`?

Points are given by their rational coordinates in the encoding of
`WantedExt.Complexity.NPComplete.PlanarKMeansWanted` (`RatCode`: the positive and negative parts
of the numerator, and the denominator) and placed in `EuclideanSpace ℝ (Fin 2)` by its `point`;
the distance is Mathlib's Euclidean `dist`. `P` is a set, so the points are distinct.
Domination is `SimpleGraph.IsDominating` from `MathlibExt.Combinatorics.SimpleGraph.Domination`.
The bound `K ≤ |P|` follows the instance class of [GT2] DOMINATING SET; for `K ≥ |P|` the
answer is trivially yes.

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
abbrev UnitDiskDominatingSetInstance := List (RatCode × RatCode) × ℕ

/-- The unit disk graph of a list of points: two distinct points are adjacent when their
Euclidean distance is at most `1`. -/
noncomputable def unitDiskGraph (P : List (RatCode × RatCode)) : SimpleGraph (Fin P.length) :=
  SimpleGraph.fromRel fun a b => dist (point P[a]) (point P[b]) ≤ 1

/-- Well-formedness of an instance: all denominators are positive, the points are distinct (as
points of the plane), and `1 ≤ K ≤ |P|`. -/
def WellFormed (i : UnitDiskDominatingSetInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p.1.2 ∧ 0 < p.2.2) ∧ (i.1.map fun p => (p.1.val, p.2.val)).Nodup ∧
    1 ≤ i.2 ∧ i.2 ≤ i.1.length

/-- The unit disk graph of `P` has a dominating set of at most `K` points. -/
def UnitDiskDominatingSetFeasible (i : UnitDiskDominatingSetInstance) : Prop :=
  ∃ D : Finset (Fin i.1.length), D.card ≤ i.2 ∧ (unitDiskGraph i.1).IsDominating ↑D

open Classical in
/-- DOMINATING SET IN UNIT DISK GRAPHS as a decision problem over bitstrings. -/
noncomputable def unitDiskDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitDiskDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ UnitDiskDominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET IN UNIT DISK GRAPHS is NP-complete.** Source: Clark, Colbourn and Johnson
(1990). -/
public theorem_wanted unitDiskDominatingSet_npComplete :
    unitDiskDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitDiskDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet
