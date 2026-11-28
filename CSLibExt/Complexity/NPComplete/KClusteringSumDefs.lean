/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-CLUSTERING SUM: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ClusteringSumOfDistancesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KClusteringSum

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

end MetaMathlibExt.Complexity.NPComplete.KClusteringSum
