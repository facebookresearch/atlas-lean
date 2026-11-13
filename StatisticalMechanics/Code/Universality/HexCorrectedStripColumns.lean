/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexCorrectedStripMassLimits
import Code.Universality.HexEndpointCriticalDivergence

namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCSTopWalkAtWidth_width_unique
    {T U : ℕ} {hT : 0 < T} {hU : 0 < U} {ts : List ℤ}
    (hwalkT : HexCSTopWalkAtWidth T hT ts)
    (hwalkU : HexCSTopWalkAtWidth U hU ts) : T = U := by
  obtain ⟨LT, _, _, c, _, hc, hcdepth, hcend⟩ := hwalkT
  obtain ⟨LU, _, _, d, _, hd, hddepth, hdend⟩ := hwalkU
  have hmid : hexAWMid c 0 = hexAWMid d 0 := hcend.symm.trans hdend
  have hcd := (hexAWMid_white_injective hc hd hmid).1
  rw [hcd] at hcdepth
  omega

def HexCSTopWalkAnyWidth (ts : List ℤ) : Prop :=
  ∃ T : ℕ, ∃ hT : 0 < T, HexCSTopWalkAtWidth T hT ts

noncomputable def hexCSTopWalkWidth
    (w : {ts : List ℤ // HexCSTopWalkAnyWidth ts}) : ℕ :=
  w.2.choose

theorem hexCSTopWalkWidth_pos
    (w : {ts : List ℤ // HexCSTopWalkAnyWidth ts}) :
    0 < hexCSTopWalkWidth w :=
  w.2.choose_spec.choose

theorem hexCSTopWalkWidth_spec
    (w : {ts : List ℤ // HexCSTopWalkAnyWidth ts}) :
    HexCSTopWalkAtWidth (hexCSTopWalkWidth w)
      (hexCSTopWalkWidth_pos w) w.1 :=
  w.2.choose_spec.choose_spec

theorem hexCSTopWalkWidth_eq
    (w : {ts : List ℤ // HexCSTopWalkAnyWidth ts})
    {T : ℕ} (hT : 0 < T) (hw : HexCSTopWalkAtWidth T hT w.1) :
    hexCSTopWalkWidth w = T :=
  hexCSTopWalkAtWidth_width_unique (hexCSTopWalkWidth_spec w) hw

noncomputable def hexCSTopFiberEquiv (T : ℕ) (hT : 0 < T) :
    {ts : List ℤ // HexCSTopWalkAtWidth T hT ts} ≃
      {w : {ts : List ℤ // HexCSTopWalkAnyWidth ts} //
        hexCSTopWalkWidth w = T} where
  toFun w := ⟨⟨w.1, T, hT, w.2⟩,
    hexCSTopWalkWidth_eq ⟨w.1, T, hT, w.2⟩ hT w.2⟩
  invFun w := ⟨w.1.1, by
    have hs := hexCSTopWalkWidth_spec w.1
    simpa [w.2] using hs⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

theorem hexCSPredicateMass_eq_tsum_subtype (P : List ℤ → Prop) :
    hexCSPredicateMass P =
      ∑' w : {ts : List ℤ // P ts},
        hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices := by
  symm
  calc
    (∑' w : {ts : List ℤ // P ts},
        hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices) =
        ∑' ts : List ℤ, (setOf P).indicator
          (fun us => hexChiE ^
            (ofTurns hexAWStart 1 us).endpointNumVertices) ts :=
      tsum_subtype (setOf P)
        (fun ts => hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices)
    _ = hexCSPredicateMass P := by
      unfold hexCSPredicateMass
      apply tsum_congr
      intro ts
      classical
      simp [hexCSPredicateWeight, Set.indicator]



theorem hecd_correctedTop_columnSum
    (T : ℕ) (hT : 0 < T) :
    hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
        hexCSTopWalkWidth T =
      hexCSPredicateMass (HexCSTopWalkAtWidth T hT) := by
  rw [hexCSPredicateMass_eq_tsum_subtype]
  unfold hecd_columnSum HexColumnEmb.fiberSum
  change (∑' i : {w : {ts : List ℤ // HexCSTopWalkAnyWidth ts} //
      hexCSTopWalkWidth w = T},
      hexEndpointSAWwt hexAWStart 1 hexChiE i.1.1) =
    ∑' w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts},
      hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices
  rw [← (hexCSTopFiberEquiv T hT).tsum_eq
    (fun w => hexEndpointSAWwt hexAWStart 1 hexChiE w.1.1)]
  apply tsum_congr
  intro w
  have hlegal : (ofTurns hexAWStart 1 w.1).EndpointIsLegalSAW :=
    w.2.choose_spec.1
  change hexEndpointSAWwt hexAWStart 1 hexChiE w.1 =
    hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices
  simp [hexEndpointSAWwt, hlegal]

theorem hecd_correctedTop_columnSum_summable
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    Summable (hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
      hexCSTopWalkWidth) :=
  hecd_columnSum_summable hexAWStart 1 HexCSTopWalkAnyWidth
    hexCSTopWalkWidth hwalk

end

end StatMech.Universality
