/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexCorrectedCriticalDivergence

namespace StatMech.Universality

open HexWalk

noncomputable section


theorem hexCSPredicateMass_sdiff
    (P Q : List ℤ → Prop)
    (hPQ : ∀ ts, P ts → Q ts)
    (hlegalQ : ∀ ts, Q ts →
      (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    hexCSPredicateMass Q = hexCSPredicateMass P +
      hexCSPredicateMass (fun ts => Q ts ∧ ¬ P ts) := by
  classical
  have hP := hexCSPredicateWeight_summable P
    (fun ts hts => hlegalQ ts (hPQ ts hts)) hwalk
  have hD := hexCSPredicateWeight_summable (fun ts => Q ts ∧ ¬ P ts)
    (fun ts hts => hlegalQ ts hts.1) hwalk
  unfold hexCSPredicateMass
  rw [← hP.tsum_add hD]
  apply tsum_congr
  intro ts
  unfold hexCSPredicateWeight
  by_cases hp : P ts
  · have hq := hPQ ts hp
    simp [hp, hq]
  · by_cases hq : Q ts
    · simp [hp, hq]
    · simp [hp, hq]



def HexCSNewSideWalk (T : ℕ) (hT : 1 ≤ T) (ts : List ℤ) : Prop :=
  HexCSSideWalkAtWidth (T + 1) (by omega) ts ∧
    ¬ HexCSSideWalkAtWidth T (by omega) ts


abbrev HexCSNextTopWalk (T : ℕ) (hT : 1 ≤ T) :=
  {ts : List ℤ // HexCSTopWalkAtWidth (T + 1) (by omega) ts}

set_option maxHeartbeats 800000 in




structure HexCSHighestCut (T : ℕ) (hT : 1 ≤ T) where
  split : {ts : List ℤ // HexCSNewSideWalk T hT ts} →
    HexCSNextTopWalk T hT × HexCSNextTopWalk T hT
  split_injective : Function.Injective split
  length_add_one : ∀ d,
    (ofTurns hexAWStart 1 (split d).1.1).endpointNumVertices +
        (ofTurns hexAWStart 1 (split d).2.1).endpointNumVertices =
      (ofTurns hexAWStart 1 d.1).endpointNumVertices + 1

theorem hexCSInfiniteSideMassAtWidth_sdiff
    (T : ℕ) (hT : 1 ≤ T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T =
      hexCSPredicateMass (HexCSNewSideWalk T hT) := by
  let P := HexCSSideWalkAtWidth T (by omega)
  let Q := HexCSSideWalkAtWidth (T + 1) (by omega)
  have hPQ : ∀ ts, P ts → Q ts := by
    intro ts hts
    obtain ⟨L, hL⟩ := hts
    exact ⟨L, hexCSSideWalk_mono (Nat.le_succ T) le_rfl hL⟩
  have hsplit := hexCSPredicateMass_sdiff P Q hPQ
    (fun ts hts => hts.choose_spec.1) hwalk
  have hsideT : hexCSInfiniteSideMassAtWidth T =
      hexCSPredicateMass P := by
    simp [hexCSInfiniteSideMassAtWidth, P, show 0 < T by omega]
  have hsideNext : hexCSInfiniteSideMassAtWidth (T + 1) =
      hexCSPredicateMass Q := by
    simp [hexCSInfiniteSideMassAtWidth, Q]
  rw [hsideT, hsideNext]
  change hexCSPredicateMass Q - hexCSPredicateMass P =
    hexCSPredicateMass (fun ts => Q ts ∧ ¬ P ts)
  linarith

theorem hexCSNewSide_tsum_eq_difference
    (T : ℕ) (hT : 1 ≤ T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    (∑' d : {ts : List ℤ // HexCSNewSideWalk T hT ts},
        hexEndpointSAWwt hexAWStart 1 hexChiE d.1) =
      hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T := by
  rw [hexCSInfiniteSideMassAtWidth_sdiff T hT hwalk,
    hexCSPredicateMass_eq_tsum_subtype]
  apply tsum_congr
  intro d
  have hlegal : (ofTurns hexAWStart 1 d.1).EndpointIsLegalSAW :=
    d.2.1.choose_spec.1
  simp [hexEndpointSAWwt, hlegal]

theorem hexCSNextTop_tsum_eq_mass
    (T : ℕ) (hT : 1 ≤ T) :
    (∑' b : HexCSNextTopWalk T hT,
        hexEndpointSAWwt hexAWStart 1 hexChiE b.1) =
      hexCSInfiniteTopMassAtWidth (T + 1) := by
  rw [show hexCSInfiniteTopMassAtWidth (T + 1) =
      hexCSPredicateMass
        (HexCSTopWalkAtWidth (T + 1) (by omega)) by
    simp [hexCSInfiniteTopMassAtWidth],
    hexCSPredicateMass_eq_tsum_subtype]
  apply tsum_congr
  intro b
  have hlegal : (ofTurns hexAWStart 1 b.1).EndpointIsLegalSAW :=
    b.2.choose_spec.1
  simp [hexEndpointSAWwt, hlegal]

namespace HexCSHighestCut

variable {T : ℕ} {hT : 1 ≤ T}




noncomputable def toHighestCut (H : HexCSHighestCut T hT)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    HexHighestCut hexChiE⁻¹ where
  D := {ts : List ℤ // HexCSNewSideWalk T hT ts}
  B := HexCSNextTopWalk T hT
  wtγ := fun d => hexEndpointSAWwt hexAWStart 1 hexChiE d.1
  wtB := fun b => hexEndpointSAWwt hexAWStart 1 hexChiE b.1
  wtγ_nn := fun d => hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le d.1
  wtB_nn := fun b => hexEndpointSAWwt_nonneg hexAWStart 1 hexChiE_pos.le b.1
  split := H.split
  split_inj := H.split_injective
  weight_bound := by
    intro d
    have hd : (ofTurns hexAWStart 1 d.1).EndpointIsLegalSAW :=
      d.2.1.choose_spec.1
    have hb1 : (ofTurns hexAWStart 1 (H.split d).1.1).EndpointIsLegalSAW :=
      (H.split d).1.2.choose_spec.1
    have hb2 : (ofTurns hexAWStart 1 (H.split d).2.1).EndpointIsLegalSAW :=
      (H.split d).2.2.choose_spec.1
    simp only [hexEndpointSAWwt, if_pos hd, if_pos hb1, if_pos hb2]
    apply le_of_eq
    rw [← pow_add, H.length_add_one d, pow_succ]
    field_simp [ne_of_gt hexChiE_pos]
  D_summable := hwalk.comp_injective Subtype.val_injective
  B_summable := hwalk.comp_injective Subtype.val_injective


theorem recurrence (H : HexCSHighestCut T hT)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T ≤
      hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2 := by
  have hbound := (H.toHighestCut hwalk).recursion_bound
    (le_of_lt hexChiE_inv_pos)
  rw [show (∑' d, (H.toHighestCut hwalk).wtγ d) =
      hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T from
      hexCSNewSide_tsum_eq_difference T hT hwalk,
    show (∑' b, (H.toHighestCut hwalk).wtB b) =
      hexCSInfiniteTopMassAtWidth (T + 1) from
      hexCSNextTop_tsum_eq_mass T hT] at hbound
  exact hbound

end HexCSHighestCut



theorem hexCS_highestCuts_recurrence
    (HC : ∀ T (hT : 1 ≤ T), HexCSHighestCut T hT)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    ∀ T, 1 ≤ T →
      hexCSInfiniteSideMassAtWidth (T + 1) -
          hexCSInfiniteSideMassAtWidth T ≤
        hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2 := by
  intro T hT
  exact (HC T hT).recurrence hwalk

end

end StatMech.Universality
