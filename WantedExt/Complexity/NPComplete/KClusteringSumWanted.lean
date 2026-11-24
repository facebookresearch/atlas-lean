/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-CLUSTERING SUM is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MINIMUM K-CLUSTERING SUM;
W. Fernandez de la Vega and C. Kenyon, "A randomized approximation scheme for metric MAX-CUT",
Journal of Computer and System Sciences 63(4) (2001), 531-541, doi:10.1006/jcss.2001.1772
(metric MAX-CUT is NP-complete; with two parts, a smallest within-cluster sum is a largest
cut, since the two add up to the fixed total);
Karthik C. S., E. Lee, Y. Rabani, C. Schwiegelshohn and S. Zhou, "A fixed parameter sublinear
time approximation scheme for metric min-sum clustering", arXiv:2610.15148 (2026), Section 1
(records that metric `k`-minsum clustering is NP-hard even for `k = 2`, by Fernandez de la Vega
and Kenyon).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ClusteringSumOfDistancesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KClusteringSum

/-!
# K-CLUSTERING SUM is NP-complete

INSTANCE: a finite set `X`, a distance `d(x, y) ∈ ℕ` for each pair `x, y ∈ X`, the distances
forming a metric (in particular satisfying the triangle inequality), a number `k` of parts,
and a positive integer `B`.
QUESTION: is there a partition of `X` into disjoint subsets `C₁, ..., C_k` such that
`∑_{i=1}^{k} ∑_{v₁, v₂ ∈ Cᵢ} d(v₁, v₂) ≤ B`?

This is CLUSTERING with the sum of within-cluster distances
(`ClusteringSumOfDistancesWanted`) restricted to metric distances. The instance type,
`Clustering.WellFormed` (a square symmetric matrix with zero diagonal, `0 < k`, `0 < B`) and
the feasibility predicate (a surjective block map onto `k` parts, all ordered pairs of a part
counted) are the parent's, unchanged; the compendium's bound `K` is the parent's `B`, and its
number of parts `k` is the parent's `K`. The added conditions make the matrix a metric, as in
`MetricKCenterWanted` and in Fernandez de la Vega and Kenyon: distinct points are at positive
distance, and the triangle inequality holds. (The compendium states only the triangle
inequality; its semi-metric version contains this one, so it is NP-hard as well.)

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's conditions (`Clustering.WellFormed`), distance
`0` exactly on the diagonal, and the triangle inequality `d(x, z) ≤ d(x, y) + d(y, z)` for all
elements `x, y, z`. -/
def WellFormed (i : Clustering.ClusteringInstance) : Prop :=
  Clustering.WellFormed i ∧
    (∀ x < i.1.length, ∀ y < i.1.length, Clustering.distance i x y = 0 ↔ x = y) ∧
    ∀ x < i.1.length, ∀ y < i.1.length, ∀ z < i.1.length,
      Clustering.distance i x z ≤ Clustering.distance i x y + Clustering.distance i y z

open Classical in
/-- K-CLUSTERING SUM as a decision problem over bitstrings. -/
noncomputable def kClusteringSumDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := Clustering.ClusteringInstance) x with
  | some i => decide (WellFormed i ∧
      ClusteringSumOfDistances.ClusteringSumOfDistancesFeasible i)
  | none => false

/-- **K-CLUSTERING SUM is NP-complete.** Source: Crescenzi and Kann, MINIMUM K-CLUSTERING SUM;
Fernandez de la Vega and Kenyon (2001). -/
public theorem_wanted kClusteringSum_npComplete :
    kClusteringSumDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kClusteringSumDec

end MetaMathlibExt.Complexity.NPComplete.KClusteringSum
