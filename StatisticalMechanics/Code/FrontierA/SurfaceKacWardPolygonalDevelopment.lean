/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.SurfaceKacWardMetricClosure
import Code.FrontierA.KacWardAdaptiveClosure











open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

universe u v





structure ClosedPolygonalFlatSurfaceGraphAtlas (g : Nat)
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
  developedConeSupport : forall {root : V}, G.Walk root root -> Finset Cone
  chartRegularTurnCorrection : forall {root : V}, G.Walk root root -> Int
  developedPolygon : forall {root : V} (p : G.Walk root root)
      (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    KWFiniteSimplePolygon p.darts.length
  chartTransitionIndex : forall {root : V} (p : G.Walk root root),
    Fin p.darts.length -> Int
  developedTurnLift : forall {root : V}
      (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k : Fin p.darts.length,
      (angle (kwGraphCycleDartLoop p (k + 1)) -
          angle (kwGraphCycleDartLoop p k)).toReal =
        (((Complex.arg ((developedPolygon p hp).edgeVector (k + 1)) :
            Real.Angle) -
          (Complex.arg ((developedPolygon p hp).edgeVector k) :
            Real.Angle)).toReal) +
        (chartTransitionIndex p k : Real) * (2 * Real.pi)
  chartIndexGaussBonnet : forall {root : V}
      (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, chartTransitionIndex p k) =
      (surfaceBaseQuadraticParity
        (surfaceSubgraphHomology edgeClass p.edges.toFinset)).val +
      2 * chartRegularTurnCorrection p +
      ∑ cone ∈ developedConeSupport p, (coneOrder cone - 1)

namespace ClosedPolygonalFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


theorem exists_developedPolygon_odd_winding
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∃ winding : Int,
      (∑ k : Fin p.darts.length,
        ((Complex.arg ((atlas.developedPolygon p hp).edgeVector (k + 1)) :
            Real.Angle) -
          (Complex.arg ((atlas.developedPolygon p hp).edgeVector k) :
            Real.Angle)).toReal : Real) =
        (winding : Real) * (2 * Real.pi) ∧ Odd winding := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let polygon := atlas.developedPolygon p hp
  let developedAngle : Fin p.darts.length -> Real.Angle := fun k =>
    Complex.arg (polygon.edgeVector k)
  obtain ⟨winding, hturn⟩ :=
    kw_totalPrincipalTurn_eq_int_mul_two_pi developedAngle id
  have hphaseVector := kwFiniteSimplePolygonPhaseSign_adaptive polygon
  rw [KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn] at hphaseVector
  have hphase : kwLoopPhaseProduct
      (fun a b => kwAngleTurnPhase (developedAngle a) (developedAngle b)) id =
        -1 := by
    simpa only [kwVectorTurnPhase, Function.comp_def, id_eq] using hphaseVector
  have hodd := kw_odd_winding_of_angleTurnPhase_eq_neg_one
    developedAngle id winding hturn hphase
  exact ⟨winding, hturn, hodd⟩



noncomputable def developedPolygonHalf
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) : Int := by
  classical
  exact if hp : p.IsCycle then
      Classical.choose
        ((atlas.exists_developedPolygon_odd_winding p hp).choose_spec.2)
    else 0

theorem developedPolygon_winding_eq_two_mul_half_add_one
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    let winding := Classical.choose
      (atlas.exists_developedPolygon_odd_winding p hp)
    winding = 2 * atlas.developedPolygonHalf p + 1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  dsimp only
  rw [developedPolygonHalf, dif_pos hp]
  exact Classical.choose_spec
    ((atlas.exists_developedPolygon_odd_winding p hp).choose_spec.2)



theorem developedGaussBonnet
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    kwClosedWalkAngleRotationNumber atlas.angle p =
      1 + (surfaceBaseQuadraticParity
        (surfaceSubgraphHomology atlas.edgeClass p.edges.toFinset)).val +
      2 * (atlas.developedPolygonHalf p +
        atlas.chartRegularTurnCorrection p) +
      ∑ cone ∈ atlas.developedConeSupport p, (atlas.coneOrder cone - 1) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let polygon := atlas.developedPolygon p hp
  let developedAngle : Fin p.darts.length -> Real.Angle := fun k =>
    Complex.arg (polygon.edgeVector k)
  let winding := Classical.choose
    (atlas.exists_developedPolygon_odd_winding p hp)
  have hpolygonTurn :=
    (atlas.exists_developedPolygon_odd_winding p hp).choose_spec.1
  have hwinding : winding = 2 * atlas.developedPolygonHalf p + 1 := by
    simpa only using
      atlas.developedPolygon_winding_eq_two_mul_half_add_one p hp
  have hsurfaceTurn :=
    kwClosedWalkAngleRotationNumber_spec atlas.angle p hp
  have hlocal :
      (∑ k : Fin p.darts.length,
        (atlas.angle (kwGraphCycleDartLoop p (k + 1)) -
        atlas.angle (kwGraphCycleDartLoop p k)).toReal : Real) =
      (∑ k : Fin p.darts.length,
        ((Complex.arg (polygon.edgeVector (k + 1)) : Real.Angle) -
        (Complex.arg (polygon.edgeVector k) : Real.Angle)).toReal : Real) +
      (∑ k : Fin p.darts.length,
        (atlas.chartTransitionIndex p k : Real)) *
        (2 * Real.pi) := by
    calc
      _ = ∑ k, (((Complex.arg
            ((atlas.developedPolygon p hp).edgeVector (k + 1)) : Real.Angle) -
          (Complex.arg
            ((atlas.developedPolygon p hp).edgeVector k) : Real.Angle)).toReal +
          (atlas.chartTransitionIndex p k : Real) * (2 * Real.pi)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact atlas.developedTurnLift p hp k
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
  have hrotationReal :
      (kwClosedWalkAngleRotationNumber atlas.angle p : Real) =
        (winding : Real) +
          (∑ k : Fin p.darts.length,
            atlas.chartTransitionIndex p k : Int) := by
    rw [hsurfaceTurn, hpolygonTurn] at hlocal
    push_cast
    nlinarith [Real.pi_pos]
  have hrotation :
      kwClosedWalkAngleRotationNumber atlas.angle p =
        winding + ∑ k : Fin p.darts.length,
          atlas.chartTransitionIndex p k := by
    exact_mod_cast hrotationReal
  have hindex := atlas.chartIndexGaussBonnet p hp
  rw [hrotation, hindex, hwinding]
  ring



noncomputable def toClosedMetricFlatSurfaceGraphAtlas
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G) :
    ClosedMetricFlatSurfaceGraphAtlas g Cone G where
  cellular := atlas.cellular
  genus_eq := atlas.genus_eq
  angle := atlas.angle
  edgeClass := atlas.edgeClass
  degree_le_three := atlas.degree_le_three
  angle_reverse := atlas.angle_reverse
  transition_nonantipodal := atlas.transition_nonantipodal
  disjoint_edge_intersection := atlas.disjoint_edge_intersection
  coneOrder := atlas.coneOrder
  coneOrder_odd := atlas.coneOrder_odd
  regularTurnCorrection := fun p =>
    atlas.developedPolygonHalf p + atlas.chartRegularTurnCorrection p
  developedConeSupport := atlas.developedConeSupport
  developedGaussBonnet := atlas.developedGaussBonnet



theorem kacWard_arf_formula
    (atlas : ClosedPolygonalFlatSurfaceGraphAtlas g Cone G)
    (weight : Sym2 V -> Real) :
    (forall lambda : SurfaceSpinStructure g,
      (1 - surfaceTwistedKacWardMatrix G
          atlas.toClosedMetricFlatSurfaceGraphAtlas.phase atlas.edgeClass
          lambda (fun edge => (weight edge : Complex))).det =
        (surfaceTwistedSectorSquare
          (surfaceGraphSectorWeight G atlas.edgeClass weight)
          lambda : Complex)) /\
    surfaceUnsignedSectorSum
        (surfaceGraphSectorWeight G atlas.edgeClass weight) =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot
              (surfaceGraphSectorWeight G atlas.edgeClass weight)
              lambda := by
  exact atlas.toClosedMetricFlatSurfaceGraphAtlas.kacWard_arf_formula weight

end ClosedPolygonalFlatSurfaceGraphAtlas

end StatMech.FrontierA
