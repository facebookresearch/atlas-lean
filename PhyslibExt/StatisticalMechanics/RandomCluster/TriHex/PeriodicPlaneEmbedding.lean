/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualPair
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicVertexGeometry

/-!
# Periodic plane embeddings of the triangular and hexagonal lattices

Packaging of the straight-segment drawings as `PeriodicPlaneEmbedding`s, given the
segment-intersection property.

## i. Overview

`TriangularStraightEdgeIntersectionProperty` (resp. the hexagonal version) says that two distinct
edge segments meet only at a common endpoint. Given it, segments of vertex-disjoint edges are
disjoint, and the straight drawing satisfies every axiom of a periodic plane embedding. The
constructions here are conditional on the intersection property; it is proved for both lattices
in `TriHex.PeriodicStraightIntersection`, which defines the unconditional embeddings.

## ii. Key results

- `TriangularStraightEdgeIntersectionProperty`, `HexagonalStraightEdgeIntersectionProperty`.
- `triangularPeriodicPlaneEmbedding_of_intersection`,
  `hexagonalPeriodicPlaneEmbedding_of_intersection` : the embeddings, given the property.

## iii. Table of contents

- A. The segment-intersection properties
- B. The periodic plane embeddings

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Ch. 6.
-/

@[expose] public section

open Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

/-! ## A. The segment-intersection properties -/

/-- Two distinct triangular edge segments meet only at a common endpoint. -/
def TriangularStraightEdgeIntersectionProperty : Prop :=
  forall {x y z w : Site 2}
    (hxy : triangularGraph.Adj x y) (hzw : triangularGraph.Adj z w)
    (p : Complex),
    Ne s(x, y) s(z, w) ->
    p ∈ Set.range (triangularStraightEdgeArc hxy) ->
    p ∈ Set.range (triangularStraightEdgeArc hzw) ->
      ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧
        triangularPlaneVertex v = p

/-- Two distinct hexagonal edge segments meet only at a common endpoint. -/
def HexagonalStraightEdgeIntersectionProperty : Prop :=
  forall {x y z w : HexVertex}
    (hxy : hexagonalGraph.Adj x y) (hzw : hexagonalGraph.Adj z w)
    (p : Complex),
    Ne s(x, y) s(z, w) ->
    p ∈ Set.range (hexagonalStraightEdgeArc hxy) ->
    p ∈ Set.range (hexagonalStraightEdgeArc hzw) ->
      ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧
        hexagonalPlaneVertex v = p

lemma triangularStraightEdgeArc_disjoint_of_intersection
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

lemma hexagonalStraightEdgeArc_disjoint_of_intersection
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

/-! ## B. The periodic plane embeddings -/

/-- The straight-segment drawing of the triangular lattice as a periodic plane embedding, given the
segment-intersection property. -/
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

/-- The straight-segment drawing of the hexagonal lattice as a periodic plane embedding, given the
segment-intersection property. -/
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
