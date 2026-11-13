/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.SurfaceKacWardPolygonalDevelopment

















open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

universe u v


noncomputable def surfaceWalkPrefixHomology {g : Nat} {V : Type u}
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root)
    (m : Nat) : SurfaceHomology g :=
  ((p.edges.take m).map edgeClass).sum


noncomputable def surfaceWalkQuadraticHeight {g : Nat} {V : Type u}
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root)
    (m : Nat) : Int :=
  (surfaceBaseQuadraticParity
    (surfaceWalkPrefixHomology edgeClass p m)).val


noncomputable def surfaceWalkQuadraticIncrement {g : Nat} {V : Type u}
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root)
    (k : Fin p.darts.length) : Int :=
  surfaceWalkQuadraticHeight edgeClass p (k.val + 1) -
    surfaceWalkQuadraticHeight edgeClass p k.val

@[simp] theorem surfaceWalkPrefixHomology_zero {g : Nat} {V : Type u}
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root) :
    surfaceWalkPrefixHomology edgeClass p 0 = 0 := by
  simp [surfaceWalkPrefixHomology]

theorem surfaceWalkPrefixHomology_length {g : Nat} {V : Type u}
    [DecidableEq V]
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root)
    (hp : p.IsCycle) :
    surfaceWalkPrefixHomology edgeClass p p.darts.length =
      surfaceSubgraphHomology edgeClass p.edges.toFinset := by
  rw [surfaceWalkPrefixHomology, SimpleGraph.Walk.length_darts,
    <- SimpleGraph.Walk.length_edges, List.take_length]
  exact (List.sum_toFinset edgeClass hp.edges_nodup).symm



theorem sum_surfaceWalkQuadraticIncrement {g : Nat} {V : Type u}
    [DecidableEq V]
    {G : SimpleGraph V} {root : V}
    (edgeClass : Sym2 V -> SurfaceHomology g) (p : G.Walk root root)
    (hp : p.IsCycle) :
    (∑ k : Fin p.darts.length,
      surfaceWalkQuadraticIncrement edgeClass p k) =
        (surfaceBaseQuadraticParity
          (surfaceSubgraphHomology edgeClass p.edges.toFinset)).val := by
  unfold surfaceWalkQuadraticIncrement
  rw [Fin.sum_univ_eq_sum_range
    (fun i => surfaceWalkQuadraticHeight edgeClass p (i + 1) -
      surfaceWalkQuadraticHeight edgeClass p i) p.darts.length]
  rw [Finset.sum_range_sub]
  simp only [surfaceWalkQuadraticHeight, surfaceWalkPrefixHomology_zero,
    surfaceBaseQuadraticParity, Prod.fst_zero, Pi.zero_apply, Prod.snd_zero,
    mul_zero, Finset.sum_const_zero, Fin.val_zero,
    Nat.cast_zero, sub_zero]
  rw [surfaceWalkPrefixHomology_length edgeClass p hp]






structure ClosedPolygonalGluingFlatSurfaceEmbedding (g : Nat)
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
  developedPolygon : forall {root : V} (p : G.Walk root root)
      (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    KWFiniteSimplePolygon p.darts.length
  

  coneAnchor : forall {root : V} (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    {cone // cone ∈ developedConeSupport p} -> Fin p.darts.length
  

  regularChartPairIndex : forall {root : V}
      (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
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
        ((surfaceWalkQuadraticIncrement edgeClass p k +
          2 * regularChartPairIndex p hp k +
          ∑ cone : {cone // cone ∈ developedConeSupport p},
            if coneAnchor p hp cone = k then coneOrder cone - 1 else 0 : Int) :
          Real) * (2 * Real.pi)

namespace ClosedPolygonalGluingFlatSurfaceEmbedding

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]



noncomputable def chartTransitionIndex
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    {root : V} (p : G.Walk root root) (k : Fin p.darts.length) : Int := by
  classical
  exact if hp : p.IsCycle then
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    surfaceWalkQuadraticIncrement embedding.edgeClass p k +
      2 * embedding.regularChartPairIndex p hp k +
      ∑ cone : {cone // cone ∈ embedding.developedConeSupport p},
        if embedding.coneAnchor p hp cone = k then
          embedding.coneOrder cone - 1 else 0
  else 0

theorem developedTurnLift_constructed
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k : Fin p.darts.length,
      (embedding.angle (kwGraphCycleDartLoop p (k + 1)) -
          embedding.angle (kwGraphCycleDartLoop p k)).toReal =
        (((Complex.arg ((embedding.developedPolygon p hp).edgeVector (k + 1)) :
            Real.Angle) -
          (Complex.arg ((embedding.developedPolygon p hp).edgeVector k) :
            Real.Angle)).toReal) +
        (embedding.chartTransitionIndex p k : Real) * (2 * Real.pi) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k
  simpa [chartTransitionIndex, hp] using embedding.developedTurnLift p hp k



noncomputable def chartRegularTurnCorrection
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    {root : V} (p : G.Walk root root) : Int := by
  classical
  exact if hp : p.IsCycle then
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∑ k : Fin p.darts.length, embedding.regularChartPairIndex p hp k
  else 0

private theorem sum_coneAnchor_fibers
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k : Fin p.darts.length,
      ∑ cone : {cone // cone ∈ embedding.developedConeSupport p},
        if embedding.coneAnchor p hp cone = k then
          embedding.coneOrder cone - 1 else 0) =
      ∑ cone ∈ embedding.developedConeSupport p,
        (embedding.coneOrder cone - 1) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rw [Finset.sum_comm]
  calc
    (∑ cone : {cone // cone ∈ embedding.developedConeSupport p},
        ∑ k : Fin p.darts.length,
          if embedding.coneAnchor p hp cone = k then
            embedding.coneOrder cone - 1 else 0) =
        ∑ cone : {cone // cone ∈ embedding.developedConeSupport p},
          (embedding.coneOrder cone - 1) := by simp
    _ = _ := Finset.sum_attach (embedding.developedConeSupport p)
      (fun cone => embedding.coneOrder cone - 1)



theorem chartIndexGaussBonnet
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, embedding.chartTransitionIndex p k) =
      (surfaceBaseQuadraticParity
        (surfaceSubgraphHomology embedding.edgeClass p.edges.toFinset)).val +
      2 * embedding.chartRegularTurnCorrection p +
      ∑ cone ∈ embedding.developedConeSupport p,
        (embedding.coneOrder cone - 1) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  calc
    (∑ k, embedding.chartTransitionIndex p k) =
        ∑ k, (surfaceWalkQuadraticIncrement embedding.edgeClass p k +
          2 * embedding.regularChartPairIndex p hp k +
          ∑ cone : {cone // cone ∈ embedding.developedConeSupport p},
            if embedding.coneAnchor p hp cone = k then
              embedding.coneOrder cone - 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      simp [chartTransitionIndex, hp]
    _ = (∑ k, surfaceWalkQuadraticIncrement embedding.edgeClass p k) +
        2 * (∑ k, embedding.regularChartPairIndex p hp k) +
        ∑ k, ∑ cone :
          {cone // cone ∈ embedding.developedConeSupport p},
            if embedding.coneAnchor p hp cone = k then
              embedding.coneOrder cone - 1 else 0 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
      rw [sum_surfaceWalkQuadraticIncrement embedding.edgeClass p hp,
        sum_coneAnchor_fibers embedding p hp]
      simp [chartRegularTurnCorrection, hp]



noncomputable def toClosedPolygonalFlatSurfaceGraphAtlas
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G) :
    ClosedPolygonalFlatSurfaceGraphAtlas g Cone G where
  cellular := embedding.cellular
  genus_eq := embedding.genus_eq
  angle := embedding.angle
  edgeClass := embedding.edgeClass
  degree_le_three := embedding.degree_le_three
  angle_reverse := embedding.angle_reverse
  transition_nonantipodal := embedding.transition_nonantipodal
  disjoint_edge_intersection := embedding.disjoint_edge_intersection
  coneOrder := embedding.coneOrder
  coneOrder_odd := embedding.coneOrder_odd
  developedConeSupport := embedding.developedConeSupport
  chartRegularTurnCorrection := embedding.chartRegularTurnCorrection
  developedPolygon := embedding.developedPolygon
  chartTransitionIndex := embedding.chartTransitionIndex
  developedTurnLift := embedding.developedTurnLift_constructed
  chartIndexGaussBonnet := embedding.chartIndexGaussBonnet



theorem developedGaussBonnet
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    kwClosedWalkAngleRotationNumber embedding.angle p =
      1 + (surfaceBaseQuadraticParity
        (surfaceSubgraphHomology embedding.edgeClass p.edges.toFinset)).val +
      2 * (embedding.toClosedPolygonalFlatSurfaceGraphAtlas.developedPolygonHalf p +
        embedding.chartRegularTurnCorrection p) +
      ∑ cone ∈ embedding.developedConeSupport p,
        (embedding.coneOrder cone - 1) := by
  simpa [toClosedPolygonalFlatSurfaceGraphAtlas] using
    embedding.toClosedPolygonalFlatSurfaceGraphAtlas.developedGaussBonnet p hp



theorem kacWard_arf_formula
    (embedding : ClosedPolygonalGluingFlatSurfaceEmbedding g Cone G)
    (weight : Sym2 V -> Real) :
    (forall lambda : SurfaceSpinStructure g,
      (1 - surfaceTwistedKacWardMatrix G
          (ClosedMetricFlatSurfaceGraphAtlas.phase
            (ClosedPolygonalFlatSurfaceGraphAtlas.toClosedMetricFlatSurfaceGraphAtlas
                embedding.toClosedPolygonalFlatSurfaceGraphAtlas))
          embedding.edgeClass lambda
          (fun edge => (weight edge : Complex))).det =
        (surfaceTwistedSectorSquare
          (surfaceGraphSectorWeight G embedding.edgeClass weight)
          lambda : Complex)) /\
    surfaceUnsignedSectorSum
        (surfaceGraphSectorWeight G embedding.edgeClass weight) =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot
              (surfaceGraphSectorWeight G embedding.edgeClass weight)
              lambda := by
  simpa [toClosedPolygonalFlatSurfaceGraphAtlas] using
    embedding.toClosedPolygonalFlatSurfaceGraphAtlas.kacWard_arf_formula weight

end ClosedPolygonalGluingFlatSurfaceEmbedding

end StatMech.FrontierA
