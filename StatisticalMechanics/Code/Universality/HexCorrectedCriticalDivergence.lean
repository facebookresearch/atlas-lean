/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexCorrectedStripInfiniteIdentity
import Code.Universality.HexCorrectedStripColumns

namespace StatMech.Universality

open HexWalk

noncomputable section


noncomputable def hexCSInfiniteSideMassAtWidth (T : ℕ) : ℝ := by
  classical
  exact if hT : 0 < T then
    hexCSPredicateMass (HexCSSideWalkAtWidth T hT)
  else 0


noncomputable def hexCSInfiniteTopMassAtWidth (T : ℕ) : ℝ := by
  classical
  exact if hT : 0 < T then
    hexCSPredicateMass (HexCSTopWalkAtWidth T hT)
  else 0

@[simp] theorem hexCSInfiniteSideMassAtWidth_succ (v : ℕ) :
    hexCSInfiniteSideMassAtWidth (v + 1) = hexCSInfiniteSideMass v := by
  simp [hexCSInfiniteSideMassAtWidth, hexCSInfiniteSideMass]

@[simp] theorem hexCSInfiniteTopMassAtWidth_succ (v : ℕ) :
    hexCSInfiniteTopMassAtWidth (v + 1) = hexCSInfiniteTopMass v := by
  simp [hexCSInfiniteTopMassAtWidth, hexCSInfiniteTopMass]

theorem hexCSInfiniteTopMassAtWidth_nonneg (T : ℕ) :
    0 ≤ hexCSInfiniteTopMassAtWidth T := by
  by_cases hT : 0 < T
  · obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
    simpa [Nat.succ_eq_add_one] using hexCSInfiniteTopMass_nonneg v
  · simp [hexCSInfiniteTopMassAtWidth, hT]

theorem hexCSInfiniteTopMassAtWidth_one_pos_of_mem
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE))
    (ts : List ℤ) (hts : HexCSTopWalkAtWidth 1 (by norm_num) ts) :
    0 < hexCSInfiniteTopMassAtWidth 1 := by
  have hsum := hexCSPredicateWeight_summable
    (HexCSTopWalkAtWidth 1 (by norm_num))
    (fun us hus => hus.choose_spec.1) hwalk
  rw [show hexCSInfiniteTopMassAtWidth 1 =
      ∑' us, hexCSPredicateWeight
        (HexCSTopWalkAtWidth 1 (by norm_num)) us by
    simp [hexCSInfiniteTopMassAtWidth, hexCSPredicateMass]]
  refine hsum.tsum_pos ?_ ts ?_
  · intro us
    unfold hexCSPredicateWeight
    split
    · exact pow_nonneg hexChiE_pos.le _
    · exact le_rfl
  · simp [hexCSPredicateWeight, hts, pow_pos hexChiE_pos]


theorem hecd_correctedTop_columnSum_eq_atWidth
    (T : ℕ) (hT : 0 < T) :
    hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
        hexCSTopWalkWidth T =
      hexCSInfiniteTopMassAtWidth T := by
  rw [hecd_correctedTop_columnSum T hT]
  simp [hexCSInfiniteTopMassAtWidth, hT]


theorem hexCS_infinite_height_identity_atWidth
    (T : ℕ) (hT : 0 < T)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE))
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
    hexCl * hexCSInfiniteSideMassAtWidth T +
        hexCSInfiniteTopMassAtWidth T = 1 := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  simpa [Nat.succ_eq_add_one] using
    hexCS_infinite_height_identity v hwalk hlocal hwindow


theorem hexCSInfiniteSideMassAtWidth_mono
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE))
    (T : ℕ) (hT : 1 ≤ T) :
    hexCSInfiniteSideMassAtWidth T ≤
      hexCSInfiniteSideMassAtWidth (T + 1) := by
  cases T with
  | zero => omega
  | succ v =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        hexCSInfiniteSideMass_mono hwalk v










theorem hexCS_critical_divergence_of_recurrence
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
    (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
    (hrec : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE) →
      ∀ T, 1 ≤ T →
        hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T ≤
          hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2)
    (htopOne : ∃ ts, HexCSTopWalkAtWidth 1 (by norm_num) ts) :
    ¬ Summable
      (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) := by
  intro hcoeff
  have hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE) :=
    (hexEndpoint_walk_summable_iff_hlc hexAWStart 1 hexChiE_pos).2 hcoeff
  have hrecWalk := hrec hwalk
  obtain ⟨topOneTurns, htopOneTurns⟩ := htopOne
  have htopOnePos : 0 < hexCSInfiniteTopMassAtWidth 1 :=
    hexCSInfiniteTopMassAtWidth_one_pos_of_mem hwalk topOneTurns htopOneTurns
  have hbdry : ∀ T, 1 ≤ T →
      hexCl * hexCSInfiniteSideMassAtWidth T +
          hexCt * (0 : ℝ) +
          hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
            hexCSTopWalkWidth T = 1 := by
    intro T hT
    have hTpos : 0 < T := by omega
    have hid := hexCS_infinite_height_identity_atWidth T hTpos
      hwalk (fun L => hlocal T L hTpos) (fun L => hwindow T L hTpos)
    rw [hecd_correctedTop_columnSum_eq_atWidth T (by omega)]
    simpa using hid
  have hrec' : ∀ T, 1 ≤ T →
      hexCSInfiniteSideMassAtWidth (T + 1) -
          hexCSInfiniteSideMassAtWidth T ≤
        hexChiE⁻¹ *
          (hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
            hexCSTopWalkWidth (T + 1)) ^ 2 := by
    intro T hT
    rw [hecd_correctedTop_columnSum_eq_atWidth (T + 1) (by omega)]
    exact hrecWalk T hT
  have htopPos : ∀ T, 1 ≤ T →
      0 < hexCSInfiniteTopMassAtWidth T := by
    intro T hT
    obtain ⟨v, rfl⟩ : ∃ v, T = 1 + v := by
      exact ⟨T - 1, by omega⟩
    induction v with
    | zero => simpa using htopOnePos
    | succ v ih =>
        have hsideMono := hexCSInfiniteSideMassAtWidth_mono hwalk
          (1 + v) (by omega)
        have hstep := hrecWalk (1 + v) (by omega)
        have hnextnn := hexCSInfiniteTopMassAtWidth_nonneg (1 + (v + 1))
        by_contra hnext
        have hnext0 : hexCSInfiniteTopMassAtWidth (1 + (v + 1)) = 0 :=
          le_antisymm (le_of_not_gt hnext) hnextnn
        have hnext0' : hexCSInfiniteTopMassAtWidth ((1 + v) + 1) = 0 := by
          simpa [Nat.add_assoc] using hnext0
        have hsideEq :
            hexCSInfiniteSideMassAtWidth ((1 + v) + 1) =
              hexCSInfiniteSideMassAtWidth (1 + v) := by
          rw [hnext0', zero_pow (by norm_num : (2 : ℕ) ≠ 0),
            mul_zero] at hstep
          exact le_antisymm (by linarith) hsideMono
        have hprevId := hexCS_infinite_height_identity_atWidth
          (1 + v) (by omega) hwalk
          (fun L => hlocal (1 + v) L (by omega))
          (fun L => hwindow (1 + v) L (by omega))
        have hnextId := hexCS_infinite_height_identity_atWidth
          (1 + (v + 1)) (by omega) hwalk
          (fun L => hlocal (1 + (v + 1)) L (by omega))
          (fun L => hwindow (1 + (v + 1)) L (by omega))
        rw [hnext0] at hnextId
        rw [show 1 + (v + 1) = (1 + v) + 1 by omega, hsideEq] at hnextId
        nlinarith [ih (by omega)]
  have hcolPos : ∀ T, 1 ≤ T →
      0 < hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
        hexCSTopWalkWidth T := by
    intro T hT
    rw [hecd_correctedTop_columnSum_eq_atWidth T (by omega)]
    exact htopPos T hT
  have hcolSum : Summable
      (hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
        hexCSTopWalkWidth) :=
    hecd_correctedTop_columnSum_summable hwalk
  have hdiv := hexZ_chi_div_recon (hlc_sawCountR hexAWStart 1)
    hexCSInfiniteSideMassAtWidth (fun _ => (0 : ℝ))
    (hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
      hexCSTopWalkWidth)
    hbdry hrec'
    (hexCSInfiniteSideMassAtWidth_mono hwalk)
    hcolPos
    (hecd_columnSum_nonneg hexAWStart 1 HexCSTopWalkAnyWidth
      hexCSTopWalkWidth)
    (fun _ => le_rfl)
    (fun hpos => by
      obtain ⟨_, _, hfalse⟩ := hpos
      exact (lt_irrefl 0 hfalse).elim)
    (fun _ => hcolSum)
  exact hdiv hcoeff

end

end StatMech.Universality
