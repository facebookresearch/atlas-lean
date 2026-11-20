/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexCorrectedStripMassLimits
import Code.Universality.HexCorrectedStripColumn

namespace StatMech.Universality

open HexWalk Filter Topology

noncomputable section


noncomputable def hexCSInfiniteSideMass (v : ℕ) : ℝ :=
  hexCSPredicateMass
    (HexCSSideWalkAtWidth (v + 1) (Nat.succ_pos v))


noncomputable def hexCSInfiniteTopMass (v : ℕ) : ℝ :=
  hexCSPredicateMass
    (HexCSTopWalkAtWidth (v + 1) (Nat.succ_pos v))

theorem hexCSInfiniteSideMass_nonneg (v : ℕ) :
    0 ≤ hexCSInfiniteSideMass v := by
  unfold hexCSInfiniteSideMass hexCSPredicateMass
  exact tsum_nonneg fun ts => by
    classical
    unfold hexCSPredicateWeight
    split
    · exact pow_nonneg (le_of_lt hexChiE_pos) _
    · exact le_rfl

theorem hexCSInfiniteTopMass_nonneg (v : ℕ) :
    0 ≤ hexCSInfiniteTopMass v := by
  unfold hexCSInfiniteTopMass hexCSPredicateMass
  exact tsum_nonneg fun ts => by
    classical
    unfold hexCSPredicateWeight
    split
    · exact pow_nonneg (le_of_lt hexChiE_pos) _
    · exact le_rfl



theorem hexCSPredicateWeight_summable
    (P : List ℤ → Prop)
    (hlegal : ∀ ts, P ts →
      (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    Summable (hexCSPredicateWeight P) := by
  classical
  apply hwalk.of_nonneg_of_le
  · intro ts
    unfold hexCSPredicateWeight
    split
    · exact pow_nonneg (le_of_lt hexChiE_pos) _
    · exact le_rfl
  · intro ts
    unfold hexCSPredicateWeight
    by_cases hp : P ts
    · have hleg := hlegal ts hp
      simp [hp, hexEndpointSAWwt, hleg]
    · rw [if_neg hp]
      exact hexEndpointSAWwt_nonneg hexAWStart 1
        (le_of_lt hexChiE_pos) ts

theorem hexCSPredicateMass_mono
    (P Q : List ℤ → Prop)
    (hPQ : ∀ ts, P ts → Q ts)
    (hlegalQ : ∀ ts, Q ts →
      (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    hexCSPredicateMass P ≤ hexCSPredicateMass Q := by
  have hQsum := hexCSPredicateWeight_summable Q hlegalQ hwalk
  have hPsum := hexCSPredicateWeight_summable P
    (fun ts hts => hlegalQ ts (hPQ ts hts)) hwalk
  unfold hexCSPredicateMass
  apply hPsum.tsum_le_tsum
  intro ts
  classical
  unfold hexCSPredicateWeight
  by_cases hp : P ts
  · rw [if_pos hp, if_pos (hPQ ts hp)]
  · rw [if_neg hp]
    by_cases hq : Q ts
    · rw [if_pos hq]
      exact pow_nonneg (le_of_lt hexChiE_pos) _
    · rw [if_neg hq]
  exact hQsum


theorem hexCSInfiniteSideMass_mono
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) (v : ℕ) :
    hexCSInfiniteSideMass v ≤ hexCSInfiniteSideMass (v + 1) := by
  unfold hexCSInfiniteSideMass
  apply hexCSPredicateMass_mono
  · intro ts hts
    obtain ⟨L, hL⟩ := hts
    exact ⟨L, hexCSSideWalk_mono (Nat.le_succ (v + 1)) le_rfl hL⟩
  · intro ts hts
    exact hts.choose_spec.1
  · exact hwalk



theorem hexCS_infinite_height_identity
    (v : ℕ)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE))
    (hlocal : ∀ L,
      HexCSLocalRelation (v + 1) L (Nat.succ_pos v))
    (hwindow : ∀ L,
      HexCSBoundaryWindowLaw (v + 1) L (Nat.succ_pos v)) :
    hexCl * hexCSInfiniteSideMass v + hexCSInfiniteTopMass v = 1 := by
  let T := v + 1
  let hT : 0 < T := Nat.succ_pos v
  have hA := hexCSA_tendsto_infiniteHeight T hT hwalk
  have hE := hexCSE_tendsto_zero T hT hwalk
  have hB := hexCSB_tendsto_infiniteHeight T hT hwalk
  have hsum : Tendsto
      (fun L => hexCl * hexCSA T L hT +
        hexCt * hexCSE T L hT + hexCSB T L hT)
      atTop
      (nhds (hexCl * hexCSInfiniteSideMass v +
        hexCt * 0 + hexCSInfiniteTopMass v)) := by
    exact ((tendsto_const_nhds.mul hA).add
      (tendsto_const_nhds.mul hE)).add hB
  have hone : Tendsto
      (fun L => hexCl * hexCSA T L hT +
        hexCt * hexCSE T L hT + hexCSB T L hT)
      atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [] with L
    exact (hexCS_finite_strip_identity_of_exit_window T L hT
      (hlocal L) (hexCS_boundaryExitLaw T L hT) (hwindow L)).symm
  have heq := tendsto_nhds_unique hsum hone
  simpa [T, hT, hexCSInfiniteSideMass, hexCSInfiniteTopMass] using heq

end

end StatMech.Universality
