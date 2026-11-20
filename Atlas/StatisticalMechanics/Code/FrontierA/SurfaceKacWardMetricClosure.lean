/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.SurfaceKacWardMetricAtlas





open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

universe u v

namespace ClosedMetricFlatSurfaceGraphAtlas

variable {g : Nat} {Cone : Type v} [Fintype Cone] [DecidableEq Cone]
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]


noncomputable def developedTurningParity
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) : Fin 2 :=
  if Even (atlas.rotationNumber p) then 0 else 1

private theorem exp_int_full_turn_half_eq_paritySign (rotation : Int) :
    Complex.exp (((((rotation : Real) * (2 * Real.pi) : Real) : Complex) *
        Complex.I) / 2) =
      (surfaceParitySign (if Even rotation then (0 : Fin 2) else 1) :
        Complex) := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' rotation
  · rw [hk]
    have heven : Even (2 * k : Int) := ⟨k, by ring⟩
    rw [if_pos heven, surfaceParitySign_zero]
    rw [show ((((((2 * k : Int) : Real) * (2 * Real.pi) : Real) : Complex) *
        Complex.I) / 2) =
      (k : Complex) * (2 * (Real.pi : Complex) * Complex.I) by
        push_cast
        ring]
    rw [Complex.exp_int_mul_two_pi_mul_I]
    norm_num
  · rw [hk]
    have hodd : Odd (2 * k + 1 : Int) := ⟨k, rfl⟩
    have hnotEven : ¬Even (2 * k + 1 : Int) :=
      Int.not_even_iff_odd.mpr hodd
    rw [if_neg hnotEven]
    norm_num [surfaceParitySign]
    rw [show ((2 * (k : Complex) + 1) *
        (2 * (Real.pi : Complex)) * Complex.I / 2) =
      (k : Complex) * (2 * (Real.pi : Complex) * Complex.I) +
        (Real.pi : Complex) * Complex.I by
        ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      Complex.exp_pi_mul_I]
    norm_num



theorem developed_phase_product
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct atlas.phase (kwGraphCycleDartLoop p) =
      (surfaceParitySign (atlas.developedTurningParity p) : Complex) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  unfold phase
  rw [kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum]
  rw [atlas.developedTurnSum p hp]
  exact exp_int_full_turn_half_eq_paritySign (atlas.rotationNumber p)

private theorem coneOrder_sub_one_even
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) (cone : Cone) :
    exists k : Int, atlas.coneOrder cone - 1 = 2 * k := by
  obtain ⟨k, hk⟩ := atlas.coneOrder_odd cone
  exact ⟨k, by omega⟩



theorem developedConeDefect_even
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) :
    exists k : Int,
      (∑ cone ∈ atlas.developedConeSupport p,
        (atlas.coneOrder cone - 1)) = 2 * k := by
  choose half hhalf using fun cone => coneOrder_sub_one_even atlas cone
  refine ⟨∑ cone ∈ atlas.developedConeSupport p, half cone, ?_⟩
  simp_rw [hhalf]
  rw [Finset.mul_sum]



theorem admissibleConeAngles
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    atlas.developedTurningParity p =
      1 + surfaceBaseQuadraticParity
        (surfaceSubgraphHomology atlas.edgeClass p.edges.toFinset) := by
  obtain ⟨coneHalf, hcone⟩ := atlas.developedConeDefect_even p
  have hgb : atlas.rotationNumber p =
      1 + (surfaceBaseQuadraticParity
        (surfaceSubgraphHomology atlas.edgeClass p.edges.toFinset)).val +
      2 * atlas.regularTurnCorrection p +
      ∑ cone ∈ atlas.developedConeSupport p,
        (atlas.coneOrder cone - 1) := by
    simpa [rotationNumber] using atlas.developedGaussBonnet p hp
  rw [hcone] at hgb
  unfold developedTurningParity
  generalize hq : surfaceBaseQuadraticParity
      (surfaceSubgraphHomology atlas.edgeClass p.edges.toFinset) = q at hgb ⊢
  fin_cases q
  · have hodd : Odd (atlas.rotationNumber p) := by
      refine ⟨atlas.regularTurnCorrection p + coneHalf, ?_⟩
      norm_num at hgb
      omega
    have hnotEven : ¬Even (atlas.rotationNumber p) :=
      Int.not_even_iff_odd.mpr hodd
    rw [if_neg hnotEven]
    norm_num
  · have heven : Even (atlas.rotationNumber p) := by
      refine ⟨1 + atlas.regularTurnCorrection p + coneHalf, ?_⟩
      norm_num at hgb
      omega
    rw [if_pos heven]
    decide



noncomputable def toClosedFlatSurfaceGraphAtlas
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) :
    ClosedFlatSurfaceGraphAtlas g G where
  cellular := atlas.cellular
  genus_eq := atlas.genus_eq
  phase := atlas.phase
  direction := atlas.direction
  edgeClass := atlas.edgeClass
  degree_le_three := atlas.degree_le_three
  direction_ne_zero := atlas.direction_ne_zero
  direction_reverse := atlas.direction_reverse
  phase_sq_eq_direction_div := fun dart next _ _ =>
    atlas.phase_sq_eq_direction_div dart next
  phase_reverse := atlas.phase_reverse
  disjoint_edge_intersection := atlas.disjoint_edge_intersection
  developedTurningParity := atlas.developedTurningParity
  developed_phase_product := atlas.developed_phase_product



theorem toClosedFlatSurfaceGraphAtlas_admissible
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) :
    atlas.toClosedFlatSurfaceGraphAtlas.AdmissibleConeAngles := by
  intro root p hp
  exact atlas.admissibleConeAngles p hp



theorem simple_cycle_holonomy
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct atlas.phase (kwGraphCycleDartLoop p) =
      -(surfaceBaseCycleCoefficient atlas.edgeClass p.edges.toFinset) := by
  exact atlas.toClosedFlatSurfaceGraphAtlas.simple_cycle_holonomy
    atlas.toClosedFlatSurfaceGraphAtlas_admissible p hp



noncomputable def toAdmissibleEmbedding
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G) :
    AdmissibleClosedFlatSurfaceEmbedding g G :=
  atlas.toClosedFlatSurfaceGraphAtlas.toAdmissibleEmbedding
    atlas.toClosedFlatSurfaceGraphAtlas_admissible



theorem kacWard_arf_formula
    (atlas : ClosedMetricFlatSurfaceGraphAtlas g Cone G)
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
    atlas.toAdmissibleEmbedding weight

end ClosedMetricFlatSurfaceGraphAtlas

end StatMech.FrontierA
