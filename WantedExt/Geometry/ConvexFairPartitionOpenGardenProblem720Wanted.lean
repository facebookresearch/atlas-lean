/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Convex fair partitions of convex polygons (Open Problem Garden 720)

Open Problem Garden, Convex 'Fair' Partitions Of Convex Polygons (R. Nandakumar and N. Ramana Rao):
given any positive integer `n`, can any convex polygon be partitioned into `n` convex pieces so that
all pieces have the same area and the same perimeter?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.Geometry.ConvexFairPartitionOpenGardenProblem720Wanted

/-!
Source: Open Problem Garden, Convex 'Fair' Partitions Of Convex Polygons (node 720; R. Nandakumar
and N. Ramana Rao),
http://www.openproblemgarden.org/op/textbf_convex_fair_partitions_of_convex_polygons. UnsolvedMath
record UM-00003076 (`OPG-720`), dataset ulamai/UnsolvedMath v1.8.0.

Only the basic question (Question 1 and the authors' conjecture) is formalized; Questions 2
(deciding when a fair partition exists and finding one minimizing the total cut length) and 3
(higher-dimensional analogues) are open-ended and omitted. The plane is `EuclideanSpace ℝ (Fin 2)`;
a convex polygon is the convex hull of finitely many points with nonempty interior. A partition into
`n` convex pieces is a family of closed convex sets with nonempty interiors, pairwise disjoint
interiors and union the polygon; area is Lebesgue measure and perimeter is the one-dimensional
Hausdorff measure of the boundary (only equality of these quantities matters, so normalizations are
irrelevant).
-/

open MeasureTheory

/-- A convex polygon in the Euclidean plane: the convex hull of finitely many points with nonempty
interior. -/
def IsConvexPolygon (P : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), P = convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin 2))) ∧
    (interior P).Nonempty

/-- `Q` is a convex fair partition of `P` into `n` pieces: closed convex pieces with nonempty
interiors and pairwise disjoint interiors, whose union is `P`, all of the same area (Lebesgue
measure) and the same perimeter (one-dimensional Hausdorff measure of the boundary). -/
def IsConvexFairPartition (P : Set (EuclideanSpace ℝ (Fin 2))) {n : ℕ}
    (Q : Fin n → Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (∀ i, Convex ℝ (Q i) ∧ IsClosed (Q i) ∧ (interior (Q i)).Nonempty) ∧ (⋃ i, Q i) = P ∧
    (∀ i j, i ≠ j → Disjoint (interior (Q i)) (interior (Q j))) ∧
    (∀ i j, volume (Q i) = volume (Q j)) ∧
    ∀ i j, μH[1] (frontier (Q i)) = μH[1] (frontier (Q j))

/-- The basic question of Nandakumar and Ramana Rao, answered affirmatively: for every positive
integer `n`, every convex polygon has a convex fair partition into `n` pieces. -/
def convexFairPartitionExists : Prop :=
  ∀ n : ℕ, 0 < n → ∀ P : Set (EuclideanSpace ℝ (Fin 2)), IsConvexPolygon P →
    ∃ Q : Fin n → Set (EuclideanSpace ℝ (Fin 2)), IsConvexFairPartition P Q

/--
Resolved true: Akopyan, Avvakumov and Karasev proved that every convex body in the plane, in
particular every convex polygon, can be partitioned into `m` convex parts of equal areas and equal
perimeters for every `m ≥ 2` (`m = 1` is trivial). Source: Open Problem Garden, Convex 'Fair'
Partitions Of Convex Polygons (node 720; R. Nandakumar and N. Ramana Rao),
http://www.openproblemgarden.org/op/textbf_convex_fair_partitions_of_convex_polygons; resolution: A.
Akopyan, S. Avvakumov and R. Karasev, Convex fair partitions into an arbitrary number of pieces,
Adv. Math. 493 (2026), 110927, doi:10.1016/j.aim.2026.110927; arXiv:1804.03057, abstract and Theorem
1.1: any convex body in the plane can be partitioned into m convex parts of equal areas and
perimeters for any integer m ≥ 2 (previously known for prime powers),
https://doi.org/10.1016/j.aim.2026.110927.
-/
public theorem_wanted convexFairPartitionExists_holds : convexFairPartitionExists

end MathlibExt.Geometry.ConvexFairPartitionOpenGardenProblem720Wanted
