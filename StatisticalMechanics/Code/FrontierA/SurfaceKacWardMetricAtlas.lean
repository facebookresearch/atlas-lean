/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.SurfaceKacWardAtlas
import Code.FrontierA.KacWardPolygonGlobalReduction










open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

universe u v


theorem kwAngleTurnPhase_sq_eq_toCircle_div (a b : Real.Angle) :
    kwAngleTurnPhase a b ^ 2 =
      (b.toCircle : Complex) / (a.toCircle : Complex) := by
  unfold kwAngleTurnPhase
  rw [pow_two, <- Complex.exp_add]
  have hexponent :
      ((((b - a).toReal : Complex) * Complex.I) / 2) +
          (((b - a).toReal : Complex) * Complex.I) / 2 =
        ((b - a).toReal : Complex) * Complex.I := by ring
  rw [hexponent]
  have hcircle :
      Complex.exp (((b - a).toReal : Complex) * Complex.I) =
        ((b - a).toCircle : Complex) := by
    calc
      Complex.exp (((b - a).toReal : Complex) * Complex.I) =
          ((((b - a).toReal : Real.Angle).toCircle : Circle) : Complex) := by
        rw [Real.Angle.toCircle_coe, Circle.coe_exp]
      _ = ((b - a).toCircle : Complex) := by
        congr 2
        exact Real.Angle.coe_toReal (b - a)
  rw [hcircle]
  simp [sub_eq_add_neg, div_eq_mul_inv]



theorem kwAngleTurnPhase_reverse_add_pi
    (a b : Real.Angle) (hne : b - a ≠ Real.pi) :
    kwAngleTurnPhase (b + Real.pi) (a + Real.pi) =
      (kwAngleTurnPhase a b)⁻¹ := by
  have hsub : (a + Real.pi) - (b + Real.pi) = -(b - a) := by abel
  have hneg : (-(b - a)).toReal = -(b - a).toReal :=
    Real.Angle.toReal_neg_eq_neg_toReal_iff.mpr hne
  unfold kwAngleTurnPhase
  rw [hsub, hneg]
  rw [show ((((-(b - a).toReal : Real) : Complex) * Complex.I) / 2) =
      -(((((b - a).toReal : Real) : Complex) * Complex.I) / 2) by
    push_cast
    ring]
  exact Complex.exp_neg _



noncomputable def kwClosedWalkAngleRotationNumber
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (angle : G.Dart -> Real.Angle) {root : V}
    (p : G.Walk root root) : Int :=
  if h : p.darts.length = 0 then 0 else by
    letI : NeZero p.darts.length := ⟨h⟩
    exact Classical.choose
      (kw_totalPrincipalTurn_eq_int_mul_two_pi angle
        (kwGraphCycleDartLoop p))


theorem kwClosedWalkAngleRotationNumber_spec
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (angle : G.Dart -> Real.Angle) {root : V}
    (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, (angle (kwGraphCycleDartLoop p (k + 1)) -
        angle (kwGraphCycleDartLoop p k)).toReal : Real) =
      (kwClosedWalkAngleRotationNumber angle p : Real) *
        (2 * Real.pi) := by
  let hne : p.darts.length ≠ 0 :=
    Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))
  letI : NeZero p.darts.length := ⟨hne⟩
  rw [kwClosedWalkAngleRotationNumber, dif_neg hne]
  exact Classical.choose_spec
    (kw_totalPrincipalTurn_eq_int_mul_two_pi angle
      (kwGraphCycleDartLoop p))




structure ClosedMetricFlatSurfaceGraphAtlas (g : Nat)
    (Cone : Type v) [Fintype Cone] [DecidableEq Cone]
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  cellular : FiniteCellularGraphEmbedding G
  genus_eq : cellular.genus = g
  angle : G.Dart -> Real.Angle
  edgeClass : Sym2 V -> SurfaceHomology g
  degree_le_three : forall vertex, G.degree vertex <= 3
  angle_reverse : forall dart, angle dart.symm = angle dart + Real.pi
  transition_nonantipodal : forall dart next,
    G.DartAdj dart next -> dart.edge ≠ next.edge ->
      angle next - angle dart ≠ Real.pi
  disjoint_edge_intersection : forall edge other : Sym2 V,
    Disjoint edge.toFinset other.toFinset ->
      surfaceIntersection (edgeClass edge) (edgeClass other) = 0
  coneOrder : Cone -> Int
  coneOrder_odd : forall cone, Odd (coneOrder cone)
  regularTurnCorrection : forall {root : V}, G.Walk root root -> Int
  developedConeSupport : forall {root : V}, G.Walk root root -> Finset Cone
  developedGaussBonnet : forall {root : V}
      (p : G.Walk root root) (hp : p.IsCycle),
    kwClosedWalkAngleRotationNumber angle p =
      1 + (surfaceBaseQuadraticParity
        (surfaceSubgraphHomology edgeClass p.edges.toFinset)).val +
      2 * regularTurnCorrection p +
      ∑ cone ∈ developedConeSupport p, (coneOrder cone - 1)

namespace ClosedMetricFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


noncomputable def rotationNumber
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) : Int :=
  kwClosedWalkAngleRotationNumber atlas.angle p


theorem developedTurnSum
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, (atlas.angle (kwGraphCycleDartLoop p (k + 1)) -
        atlas.angle (kwGraphCycleDartLoop p k)).toReal : Real) =
      (atlas.rotationNumber p : Real) * (2 * Real.pi) := by
  exact kwClosedWalkAngleRotationNumber_spec atlas.angle p hp


noncomputable def phase (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    (dart next : G.Dart) : Complex :=
  kwAngleTurnPhase (atlas.angle dart) (atlas.angle next)


noncomputable def direction
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    (dart : G.Dart) : Complex :=
  atlas.angle dart |>.toCircle

theorem direction_ne_zero
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) (dart : G.Dart) :
    atlas.direction dart ≠ 0 := by
  exact Circle.coe_ne_zero _

theorem direction_reverse
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) (dart : G.Dart) :
    atlas.direction dart.symm = -atlas.direction dart := by
  unfold direction
  rw [atlas.angle_reverse]
  simp [Real.Angle.coe_toCircle]

theorem phase_sq_eq_direction_div
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    (dart next : G.Dart) :
    atlas.phase dart next ^ 2 =
      atlas.direction next / atlas.direction dart := by
  exact kwAngleTurnPhase_sq_eq_toCircle_div _ _

theorem phase_reverse
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    (dart next : G.Dart) (hadj : G.DartAdj dart next)
    (hne : dart.edge ≠ next.edge) :
    atlas.phase next.symm dart.symm = (atlas.phase dart next)⁻¹ := by
  unfold phase
  rw [atlas.angle_reverse, atlas.angle_reverse]
  exact kwAngleTurnPhase_reverse_add_pi _ _
    (atlas.transition_nonantipodal dart next hadj hne)

end ClosedMetricFlatSurfaceGraphAtlas

end StatMech.FrontierA
