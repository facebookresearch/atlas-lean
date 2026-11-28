/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISTANCE-d PARTITION OF POINTS IN THE PLANE: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 182-195,
doi:10.1016/0196-6774(82)90018-9, problem [3] DISTANCE-d PARTITION OF POINTS IN THE PLANE
(reference: S. Burr, private communication; transformation from PLANAR GRAPH 3-COLORABILITY;
the original was not available);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, Section 2 (the result "should also be attributed to J. Orlin",
private communication).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DistanceDPartitionPointsPlane

open GeometricTravelingSalesman (point)

/-- An instance: the points of `P` (each a pair of integer coordinates in positive/negative-part
form), the distance `d` and the number of sets `K`. -/
abbrev DistanceDPartitionPointsPlaneInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ × ℕ

/-- Well-formedness of an instance: the points are distinct, and `d` and `K` are positive. -/
def WellFormed (i : DistanceDPartitionPointsPlaneInstance) : Prop :=
  (i.1.map point).Nodup ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- Some partition of the points into `K` nonempty sets (a surjective map `c` to `Fin K`) puts
two distinct points in the same set only when their Euclidean distance exceeds `d`:
`d² < (u₁ - v₁)² + (u₂ - v₂)²`. -/
def DistanceDPartitionPointsPlaneFeasible (i : DistanceDPartitionPointsPlaneInstance) : Prop :=
  ∃ c : Fin i.1.length → Fin i.2.2, Function.Surjective c ∧ ∀ a b, a ≠ b → c a = c b →
    (i.2.1 : ℤ) ^ 2 < ((point i.1[a]).1 - (point i.1[b]).1) ^ 2 +
      ((point i.1[a]).2 - (point i.1[b]).2) ^ 2

open Classical in
/-- DISTANCE-d PARTITION OF POINTS IN THE PLANE as a decision problem over bitstrings. -/
noncomputable def distanceDPartitionPointsPlaneDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DistanceDPartitionPointsPlaneInstance) x with
  | some i => decide (WellFormed i ∧ DistanceDPartitionPointsPlaneFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DistanceDPartitionPointsPlane
