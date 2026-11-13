/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexCorrectedSideDepth
import Code.Universality.HexCorrectedShiftedDivergence
import Code.Universality.HexCorrectedStripExteriorPeriod
import Code.Universality.HexLiteralHWDepthCompletion

namespace StatMech.Universality

open HexWalk

noncomputable section


abbrev HexCSCompletedTopWalk (T : ℕ) (hT : 1 ≤ T) :=
  {ts : List ℤ // HexCSTopWalkAtWidth (T + 2) (by omega) ts}


noncomputable def hexCSCompletedSplit
    (T : ℕ) (hT : 1 ≤ T)
    (d : {ts : List ℤ // HexCSNewSideWalk T hT ts}) :
    HexCSCompletedTopWalk T hT × HexCSCompletedTopWalk T hT := by
  let G := hexCSNewSideDepthData T hT d
  let p := hlhda_completedPair d.1 G.legal
  refine ⟨⟨p.1, ?_⟩, ⟨p.2, ?_⟩⟩
  · have hp := hlhda_completedPrefix_mem_topAtWidth
      G.legal (T + 1) (by omega) G.depth_nonneg G.cut_depth
    simpa [p, hlhda_completedPair] using hp
  · have hs := hlhda_completedSuffix_mem_topAtWidth
      G.legal (T + 1) (by omega) G.depth_nonneg
      G.terminal_depth_zero G.terminal_white G.cut_depth
    simpa [p, hlhda_completedPair] using hs

theorem hexCSCompletedSplit_injective
    (T : ℕ) (hT : 1 ≤ T) :
    Function.Injective (hexCSCompletedSplit T hT) := by
  intro d e hde
  let Gd := hexCSNewSideDepthData T hT d
  let Ge := hexCSNewSideDepthData T hT e
  apply Subtype.ext
  apply hlhda_completedPair_injective Gd.legal Ge.legal
  apply Prod.ext
  · have h := congrArg (fun p => p.1.1) hde
    simpa [hexCSCompletedSplit, hlhda_completedPair, Gd, Ge] using h
  · have h := congrArg (fun p => p.2.1) hde
    simpa [hexCSCompletedSplit, hlhda_completedPair, Gd, Ge] using h

theorem hexCSCompletedSplit_length
    (T : ℕ) (hT : 1 ≤ T)
    (d : {ts : List ℤ // HexCSNewSideWalk T hT ts}) :
    (ofTurns hexAWStart 1 (hexCSCompletedSplit T hT d).1.1).endpointNumVertices +
        (ofTurns hexAWStart 1
          (hexCSCompletedSplit T hT d).2.1).endpointNumVertices =
      (ofTurns hexAWStart 1 d.1).endpointNumVertices + 5 := by
  let G := hexCSNewSideDepthData T hT d
  have hlen := hlhda_completedPair_length d.1 G.legal
  simpa [hexCSCompletedSplit, hlhda_completedPair,
    HexWalk.endpointNumVertices, G] using hlen

set_option maxHeartbeats 800000 in


structure HexCSCompletedHighestCut (T : ℕ) (hT : 1 ≤ T) where
  split : {ts : List ℤ // HexCSNewSideWalk T hT ts} →
    HexCSCompletedTopWalk T hT × HexCSCompletedTopWalk T hT
  split_injective : Function.Injective split
  length_add_five : ∀ d,
    (ofTurns hexAWStart 1 (split d).1.1).endpointNumVertices +
        (ofTurns hexAWStart 1 (split d).2.1).endpointNumVertices =
      (ofTurns hexAWStart 1 d.1).endpointNumVertices + 5


noncomputable def hexCSCompletedHighestCut
    (T : ℕ) (hT : 1 ≤ T) : HexCSCompletedHighestCut T hT where
  split := hexCSCompletedSplit T hT
  split_injective := hexCSCompletedSplit_injective T hT
  length_add_five := hexCSCompletedSplit_length T hT

theorem hexCSCompletedTop_tsum_eq_mass
    (T : ℕ) (hT : 1 ≤ T) :
    (∑' b : HexCSCompletedTopWalk T hT,
        hexEndpointSAWwt hexAWStart 1 hexChiE b.1) =
      hexCSInfiniteTopMassAtWidth (T + 2) := by
  rw [show hexCSInfiniteTopMassAtWidth (T + 2) =
      hexCSPredicateMass
        (HexCSTopWalkAtWidth (T + 2) (by omega)) by
    simp [hexCSInfiniteTopMassAtWidth],
    hexCSPredicateMass_eq_tsum_subtype]
  apply tsum_congr
  intro b
  have hlegal : (ofTurns hexAWStart 1 b.1).EndpointIsLegalSAW :=
    b.2.choose_spec.1
  simp [hexEndpointSAWwt, hlegal]



noncomputable def hexCSCompletedAsymmetricCut
    (T : ℕ) (hT : 1 ≤ T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    HexAsymmetricHighestCut (hexChiE⁻¹ ^ 5) where
  D := {ts : List ℤ // HexCSNewSideWalk T hT ts}
  B₁ := HexCSCompletedTopWalk T hT
  B₂ := HexCSCompletedTopWalk T hT
  wtγ := fun d => hexEndpointSAWwt hexAWStart 1 hexChiE d.1
  wtB₁ := fun b => hexEndpointSAWwt hexAWStart 1 hexChiE b.1
  wtB₂ := fun b => hexEndpointSAWwt hexAWStart 1 hexChiE b.1
  wtγ_nn := fun d => hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le d.1
  wtB₁_nn := fun b => hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le b.1
  wtB₂_nn := fun b => hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le b.1
  split := hexCSCompletedSplit T hT
  split_injective := hexCSCompletedSplit_injective T hT
  weight_bound := by
    intro d
    have hd : (ofTurns hexAWStart 1 d.1).EndpointIsLegalSAW :=
      d.2.1.choose_spec.1
    have hb₁ :
        (ofTurns hexAWStart 1 (hexCSCompletedSplit T hT d).1.1).EndpointIsLegalSAW :=
      (hexCSCompletedSplit T hT d).1.2.choose_spec.1
    have hb₂ :
        (ofTurns hexAWStart 1 (hexCSCompletedSplit T hT d).2.1).EndpointIsLegalSAW :=
      (hexCSCompletedSplit T hT d).2.2.choose_spec.1
    simp only [hexEndpointSAWwt, if_pos hd, if_pos hb₁, if_pos hb₂]
    apply le_of_eq
    rw [← pow_add, hexCSCompletedSplit_length T hT d]
    simp only [endpointNumVertices]
    rw [pow_add]
    field_simp [ne_of_gt hexChiE_pos]
  D_summable := hwalk.comp_injective Subtype.val_injective
  B₁_summable := hwalk.comp_injective Subtype.val_injective
  B₂_summable := hwalk.comp_injective Subtype.val_injective


theorem hexCS_completedHighestCut_recurrence
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    ∀ T, 1 ≤ T →
      hexCSInfiniteSideMassAtWidth (T + 1) -
          hexCSInfiniteSideMassAtWidth T ≤
        (hexChiE⁻¹ ^ 5) *
          (hexCSInfiniteTopMassAtWidth (T + 2) *
            hexCSInfiniteTopMassAtWidth (T + 2)) := by
  intro T hT
  have hbound := (hexCSCompletedAsymmetricCut T hT hwalk).recursion_bound
    (le_of_lt (pow_pos hexChiE_inv_pos 5))
  rw [show (∑' d, (hexCSCompletedAsymmetricCut T hT hwalk).wtγ d) =
      hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T from
      hexCSNewSide_tsum_eq_difference T hT hwalk,
    show (∑' b, (hexCSCompletedAsymmetricCut T hT hwalk).wtB₁ b) =
      hexCSInfiniteTopMassAtWidth (T + 2) from
      hexCSCompletedTop_tsum_eq_mass T hT,
    show (∑' b, (hexCSCompletedAsymmetricCut T hT hwalk).wtB₂ b) =
      hexCSInfiniteTopMassAtWidth (T + 2) from
      hexCSCompletedTop_tsum_eq_mass T hT] at hbound
  exact hbound


theorem hexCS_critical_divergence_of_completedHighestCut
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT) :
    ¬ Summable
      (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) := by
  apply hexCS_critical_divergence_of_shifted_recurrence
    (hexChiE⁻¹ ^ 5) (pow_pos hexChiE_inv_pos 5)
    2 2 (by omega) (by omega)
    hlocal hexCSBoundaryWindowLaw_unconditional
    hexCS_completedHighestCut_recurrence
    hexCSTopWalkAtWidth_one_nonempty

end

end StatMech.Universality
