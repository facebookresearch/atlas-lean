/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexCorrectedStripFamilyMass
import Code.Universality.HexEndpointAggregation

namespace StatMech.Universality

open HexWalk Filter Topology

noncomputable section

noncomputable def hexCSPredicateWeight
    (P : List ℤ → Prop) (ts : List ℤ) : ℝ := by
  classical
  exact if P ts then
    hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices else 0

noncomputable def hexCSPredicateMass (P : List ℤ → Prop) : ℝ :=
  ∑' ts : List ℤ, hexCSPredicateWeight P ts

theorem hexCSClassWalkMass_eq_predicateMass
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) :
    hexCSClassWalkMass T L hT cls =
      hexCSPredicateMass (HexCSClassWalk T L hT cls) := by
  rfl

theorem hexCSA_eq_sideWalkMass (T L : ℕ) (hT : 0 < T) :
    hexCSA T L hT = hexCSPredicateMass (HexCSSideWalk T L hT) := by
  rw [hexCSA_eq_classWalkMass, hexCSClassWalkMass_eq_predicateMass]
  unfold hexCSPredicateMass
  apply tsum_congr
  intro ts
  classical
  unfold hexCSPredicateWeight
  rw [if_congr (hexCSClassWalk_side_iff T L hT ts) rfl rfl]

theorem hexCSE_eq_slantWalkMass (T L : ℕ) (hT : 0 < T) :
    hexCSE T L hT = hexCSPredicateMass (HexCSSlantWalk T L hT) := by
  rw [hexCSE_eq_classWalkMass, hexCSClassWalkMass_eq_predicateMass]
  unfold hexCSPredicateMass
  apply tsum_congr
  intro ts
  classical
  unfold hexCSPredicateWeight
  rw [if_congr (hexCSClassWalk_slant_iff T L hT ts) rfl rfl]

theorem hexCSB_eq_topWalkMass (T L : ℕ) (hT : 0 < T) :
    hexCSB T L hT = hexCSPredicateMass (HexCSTopWalk T L hT) := by
  rw [hexCSB_eq_classWalkMass, hexCSClassWalkMass_eq_predicateMass]
  unfold hexCSPredicateMass
  apply tsum_congr
  intro ts
  classical
  unfold hexCSPredicateWeight
  rw [if_congr (hexCSClassWalk_top_iff T L hT ts) rfl rfl]

def HexCSSideWalkAtWidth (T : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  ∃ L, HexCSSideWalk T L hT ts

theorem hexCSPredicateMass_tendsto_of_dominated
    (P : ℕ → List ℤ → Prop) (Pinf : List ℤ → Prop)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE))
    (hlegal : ∀ L ts, P L ts →
      (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hpoint : ∀ ts,
      Tendsto (fun L => hexCSPredicateWeight (P L) ts) atTop
        (nhds (hexCSPredicateWeight Pinf ts))) :
    Tendsto (fun L => hexCSPredicateMass (P L)) atTop
      (nhds (hexCSPredicateMass Pinf)) := by
  unfold hexCSPredicateMass
  apply tendsto_tsum_of_dominated_convergence hwalk
  · exact hpoint
  · filter_upwards [] with L ts
    classical
    unfold hexCSPredicateWeight
    by_cases hp : P L ts
    · have hleg := hlegal L ts hp
      rw [if_pos hp, hexEndpointSAWwt, if_pos hleg, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hexChiE_pos.le _)]
    · rw [if_neg hp, norm_zero]
      exact hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le ts

theorem hexCSSideMass_tendsto
    (T : ℕ) (hT : 0 < T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    Tendsto (fun L => hexCSPredicateMass (HexCSSideWalk T L hT))
      atTop (nhds (hexCSPredicateMass (HexCSSideWalkAtWidth T hT))) := by
  apply hexCSPredicateMass_tendsto_of_dominated
    (fun L => HexCSSideWalk T L hT) (HexCSSideWalkAtWidth T hT)
    hwalk (fun L ts h => h.1)
  intro ts
  classical
  unfold hexCSPredicateWeight
  by_cases hmem : HexCSSideWalkAtWidth T hT ts
  · obtain ⟨L0, hL0⟩ := hmem
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop L0] with L hL
    rw [if_pos (hexCSSideWalk_mono le_rfl hL hL0),
      if_pos ⟨L0, hL0⟩]
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with L
    rw [if_neg (fun h => hmem ⟨L, h⟩), if_neg hmem]

theorem hexCSTopMass_tendsto
    (T : ℕ) (hT : 0 < T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    Tendsto (fun L => hexCSPredicateMass (HexCSTopWalk T L hT))
      atTop (nhds (hexCSPredicateMass (HexCSTopWalkAtWidth T hT))) := by
  apply hexCSPredicateMass_tendsto_of_dominated
    (fun L => HexCSTopWalk T L hT) (HexCSTopWalkAtWidth T hT)
    hwalk (fun L ts h => h.1)
  intro ts
  classical
  unfold hexCSPredicateWeight
  by_cases hmem : HexCSTopWalkAtWidth T hT ts
  · obtain ⟨L0, hL0⟩ := hmem
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop L0] with L hL
    rw [if_pos (hexCSTopWalk_mono_L hL hL0), if_pos ⟨L0, hL0⟩]
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with L
    rw [if_neg (fun h => hmem ⟨L, h⟩), if_neg hmem]

theorem hexCSSlantMass_tendsto_zero
    (T : ℕ) (hT : 0 < T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    Tendsto (fun L => hexCSPredicateMass (HexCSSlantWalk T L hT))
      atTop (nhds 0) := by
  have hlim := hexCSPredicateMass_tendsto_of_dominated
    (fun L => HexCSSlantWalk T L hT) (fun _ => False)
    hwalk (fun L ts h => h.1) (by
      intro ts
      classical
      unfold hexCSPredicateWeight
      by_cases hmem : HexCSSlantWalkAtWidth T hT ts
      · let w : {us : List ℤ // HexCSSlantWalkAtWidth T hT us} := ⟨ts, hmem⟩
        let L0 := hexCSSlantWalkHeight w
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop L0] with L hL
        have hnot : ¬ HexCSSlantWalk T L hT ts := by
          intro hs
          have heq := hexCSSlantWalkHeight_eq w hs
          dsimp [L0] at hL
          omega
        simp [hnot]
      · apply tendsto_const_nhds.congr'
        filter_upwards [] with L
        rw [if_neg (fun h => hmem ⟨L, h⟩), if_neg (by simp)])
  simpa [hexCSPredicateMass, hexCSPredicateWeight] using hlim

theorem hexCSA_tendsto_infiniteHeight
    (T : ℕ) (hT : 0 < T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    Tendsto (fun L => hexCSA T L hT) atTop
      (nhds (hexCSPredicateMass (HexCSSideWalkAtWidth T hT))) := by
  simpa only [hexCSA_eq_sideWalkMass] using
    hexCSSideMass_tendsto T hT hwalk

theorem hexCSB_tendsto_infiniteHeight
    (T : ℕ) (hT : 0 < T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    Tendsto (fun L => hexCSB T L hT) atTop
      (nhds (hexCSPredicateMass (HexCSTopWalkAtWidth T hT))) := by
  simpa only [hexCSB_eq_topWalkMass] using
    hexCSTopMass_tendsto T hT hwalk

theorem hexCSE_tendsto_zero
    (T : ℕ) (hT : 0 < T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    Tendsto (fun L => hexCSE T L hT) atTop (nhds 0) := by
  simpa only [hexCSE_eq_slantWalkMass] using
    hexCSSlantMass_tendsto_zero T hT hwalk



theorem hexCS_infiniteHeight_boundary_identity
    (T : ℕ) (hT : 0 < T)
    (hfinite : ∀ L,
      hexCl * hexCSA T L hT + hexCt * hexCSE T L hT +
        hexCSB T L hT = 1)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    hexCl * hexCSPredicateMass (HexCSSideWalkAtWidth T hT) +
      hexCSPredicateMass (HexCSTopWalkAtWidth T hT) = 1 := by
  have hA := hexCSA_tendsto_infiniteHeight T hT hwalk
  have hE := hexCSE_tendsto_zero T hT hwalk
  have hB := hexCSB_tendsto_infiniteHeight T hT hwalk
  have hsum : Tendsto
      (fun L => hexCl * hexCSA T L hT + hexCt * hexCSE T L hT +
        hexCSB T L hT) atTop
      (nhds (hexCl * hexCSPredicateMass (HexCSSideWalkAtWidth T hT) +
        hexCt * 0 + hexCSPredicateMass (HexCSTopWalkAtWidth T hT))) := by
    exact ((tendsto_const_nhds.mul hA).add
      (tendsto_const_nhds.mul hE)).add hB
  have hone : Tendsto
      (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hsum_one : Tendsto
      (fun L => hexCl * hexCSA T L hT + hexCt * hexCSE T L hT +
        hexCSB T L hT) atTop (nhds 1) := by
    convert hone using 1
    funext L
    exact hfinite L
  have heq := tendsto_nhds_unique hsum hsum_one
  simpa using heq

end

end StatMech.Universality
