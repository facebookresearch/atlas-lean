/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarDualPair
import Code.FK.TriHexPeriodicVertexGeometry











open Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice



def TriangularStraightEdgeIntersectionProperty : Prop :=
  forall {x y z w : Site 2}
    (hxy : triangularGraph.Adj x y) (hzw : triangularGraph.Adj z w)
    (p : Complex),
    Ne s(x, y) s(z, w) ->
    p ∈ Set.range (triangularStraightEdgeArc hxy) ->
    p ∈ Set.range (triangularStraightEdgeArc hzw) ->
      ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧
        triangularPlaneVertex v = p



def HexagonalStraightEdgeIntersectionProperty : Prop :=
  forall {x y z w : HexVertex}
    (hxy : hexagonalGraph.Adj x y) (hzw : hexagonalGraph.Adj z w)
    (p : Complex),
    Ne s(x, y) s(z, w) ->
    p ∈ Set.range (hexagonalStraightEdgeArc hxy) ->
    p ∈ Set.range (hexagonalStraightEdgeArc hzw) ->
      ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧
        hexagonalPlaneVertex v = p

theorem triangularStraightEdgeArc_disjoint_of_intersection
    (hinter : TriangularStraightEdgeIntersectionProperty)
    {x y z w : Site 2}
    (hxy : triangularGraph.Adj x y) (hzw : triangularGraph.Adj z w)
    (hxz : Ne x z) (hxw : Ne x w) (hyz : Ne y z) (hyw : Ne y w) :
    Disjoint (Set.range (triangularStraightEdgeArc hxy))
      (Set.range (triangularStraightEdgeArc hzw)) := by
  rw [Set.disjoint_left]
  intro p hp hp'
  have hedge : Ne s(x, y) s(z, w) := by
    intro he
    rw [Sym2.eq_iff] at he
    rcases he with h | h
    · exact hxz h.1
    · exact hxw h.1
  obtain ⟨v, hvxy, hvzw, _hv⟩ := hinter hxy hzw p hedge hp hp'
  rcases hvxy with rfl | rfl
  · rcases hvzw with rfl | rfl
    · exact hxz rfl
    · exact hxw rfl
  · rcases hvzw with rfl | rfl
    · exact hyz rfl
    · exact hyw rfl

theorem hexagonalStraightEdgeArc_disjoint_of_intersection
    (hinter : HexagonalStraightEdgeIntersectionProperty)
    {x y z w : HexVertex}
    (hxy : hexagonalGraph.Adj x y) (hzw : hexagonalGraph.Adj z w)
    (hxz : Ne x z) (hxw : Ne x w) (hyz : Ne y z) (hyw : Ne y w) :
    Disjoint (Set.range (hexagonalStraightEdgeArc hxy))
      (Set.range (hexagonalStraightEdgeArc hzw)) := by
  rw [Set.disjoint_left]
  intro p hp hp'
  have hedge : Ne s(x, y) s(z, w) := by
    intro he
    rw [Sym2.eq_iff] at he
    rcases he with h | h
    · exact hxz h.1
    · exact hxw h.1
  obtain ⟨v, hvxy, hvzw, _hv⟩ := hinter hxy hzw p hedge hp hp'
  rcases hvxy with rfl | rfl
  · rcases hvzw with rfl | rfl
    · exact hxz rfl
    · exact hxw rfl
  · rcases hvzw with rfl | rfl
    · exact hyz rfl
    · exact hyw rfl



noncomputable def triangularPeriodicPlaneEmbedding_of_intersection
    (hinter : TriangularStraightEdgeIntersectionProperty) :
    PeriodicPlaneEmbedding triangular where
  vertex := triangularPlaneVertex
  period := triHexPlanePeriod
  period_injective := triHexPlanePeriod_injective
  coordinates := triHexPlaneCoordinates
  coordinates_period := triHexPlaneCoordinates_period
  vertex_shift := triangularPlaneVertex_shift
  proper := triangularPlaneVertex_bounded_finite
  edgeArc := triangularStraightEdgeArc
  edgeArc_injective := triangularStraightEdgeArc_injective
  edgeArc_symm := triangularStraightEdgeArc_symm
  edgeArc_shift := triangularStraightEdgeArc_shift
  edgeArc_intersection := hinter
  edgeArc_disjoint :=
    triangularStraightEdgeArc_disjoint_of_intersection hinter
  edgeArc_locallyFinite := triangularStraightEdgeArc_locallyFinite



noncomputable def hexagonalPeriodicPlaneEmbedding_of_intersection
    (hinter : HexagonalStraightEdgeIntersectionProperty) :
    PeriodicPlaneEmbedding hexagonal where
  vertex := hexagonalPlaneVertex
  period := triHexPlanePeriod
  period_injective := triHexPlanePeriod_injective
  coordinates := triHexPlaneCoordinates
  coordinates_period := triHexPlaneCoordinates_period
  vertex_shift := hexagonalPlaneVertex_shift
  proper := hexagonalPlaneVertex_bounded_finite
  edgeArc := hexagonalStraightEdgeArc
  edgeArc_injective := hexagonalStraightEdgeArc_injective
  edgeArc_symm := hexagonalStraightEdgeArc_symm
  edgeArc_shift := hexagonalStraightEdgeArc_shift
  edgeArc_intersection := hinter
  edgeArc_disjoint :=
    hexagonalStraightEdgeArc_disjoint_of_intersection hinter
  edgeArc_locallyFinite := hexagonalStraightEdgeArc_locallyFinite

end StatMech.FK.PeriodicPlanar
