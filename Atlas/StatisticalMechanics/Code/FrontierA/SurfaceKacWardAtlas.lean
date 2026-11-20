/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.SurfaceKacWardLocalGeometry


















open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

universe u




structure ClosedFlatSurfaceGraphAtlas (g : Nat)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  cellular : FiniteCellularGraphEmbedding G
  genus_eq : cellular.genus = g
  phase : G.Dart -> G.Dart -> Complex
  direction : G.Dart -> Complex
  edgeClass : Sym2 V -> SurfaceHomology g
  degree_le_three : forall vertex, G.degree vertex <= 3
  direction_ne_zero : forall dart, direction dart ≠ 0
  direction_reverse : forall dart,
    direction dart.symm = -direction dart
  phase_sq_eq_direction_div : forall dart next,
    G.DartAdj dart next -> dart.edge ≠ next.edge ->
      phase dart next ^ 2 = direction next / direction dart
  phase_reverse : forall dart next,
    G.DartAdj dart next -> dart.edge ≠ next.edge ->
      phase next.symm dart.symm = (phase dart next)⁻¹
  disjoint_edge_intersection : forall edge other : Sym2 V,
    Disjoint edge.toFinset other.toFinset ->
      surfaceIntersection (edgeClass edge) (edgeClass other) = 0
  developedTurningParity : forall {root : V}, G.Walk root root -> Fin 2
  developed_phase_product : forall {root : V}
      (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) =
      (surfaceParitySign (developedTurningParity p) : Complex)




def ClosedFlatSurfaceGraphAtlas.AdmissibleConeAngles
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G) : Prop :=
  forall {root : V} (p : G.Walk root root), p.IsCycle ->
    atlas.developedTurningParity p =
      1 + surfaceBaseQuadraticParity
        (surfaceSubgraphHomology atlas.edgeClass p.edges.toFinset)



theorem ClosedFlatSurfaceGraphAtlas.phase_sq_transport
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G)
    (dart next : G.Dart) (hadj : G.DartAdj dart next)
    (hne : dart.edge ≠ next.edge) :
    atlas.phase dart next ^ 2 * atlas.direction dart =
      atlas.direction next := by
  rw [atlas.phase_sq_eq_direction_div dart next hadj hne]
  exact div_mul_cancel₀ _ (atlas.direction_ne_zero dart)



noncomputable def ClosedFlatSurfaceGraphAtlas.toLocalSpinorGeometry
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G) :
    SurfaceLocalSpinorGeometry g G where
  cellular := atlas.cellular
  genus_eq := atlas.genus_eq
  phase := atlas.phase
  direction := atlas.direction
  edgeClass := atlas.edgeClass
  degree_le_three := atlas.degree_le_three
  direction_ne_zero := atlas.direction_ne_zero
  direction_reverse := atlas.direction_reverse
  phase_sq_transport := atlas.phase_sq_transport
  phase_reverse := atlas.phase_reverse
  disjoint_edge_intersection := atlas.disjoint_edge_intersection

theorem surfaceParitySign_one_add (z : Fin 2) :
    (surfaceParitySign (1 + z) : Complex) =
      -(surfaceParitySign z : Complex) := by
  fin_cases z <;> norm_num [surfaceParitySign, Fin.val_add]



theorem ClosedFlatSurfaceGraphAtlas.simple_cycle_holonomy
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G)
    (hadmissible : atlas.AdmissibleConeAngles)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct atlas.phase (kwGraphCycleDartLoop p) =
      -(surfaceBaseCycleCoefficient atlas.edgeClass p.edges.toFinset) := by
  rw [atlas.developed_phase_product p hp, hadmissible p hp]
  unfold surfaceBaseCycleCoefficient
  exact surfaceParitySign_one_add _




noncomputable def ClosedFlatSurfaceGraphAtlas.toAdmissibleEmbedding
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G)
    (hadmissible : atlas.AdmissibleConeAngles) :
    AdmissibleClosedFlatSurfaceEmbedding g G where
  geometry := atlas.toLocalSpinorGeometry
  developed_simple_cycle_holonomy := atlas.simple_cycle_holonomy hadmissible



theorem closedFlatSurfaceAtlas_kacWard_arf_formula
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G)
    (hadmissible : atlas.AdmissibleConeAngles)
    (weight : Sym2 V -> Real) :
    (forall lambda : SurfaceSpinStructure g,
      (1 - surfaceTwistedKacWardMatrix G atlas.phase atlas.edgeClass lambda
          (fun edge => (weight edge : Complex))).det =
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
  exact admissible_closedFlatSurface_kacWard_arf_formula G
    (atlas.toAdmissibleEmbedding hadmissible) weight

end StatMech.FrontierA
