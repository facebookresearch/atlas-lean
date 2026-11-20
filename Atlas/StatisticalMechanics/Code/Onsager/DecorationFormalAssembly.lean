/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalEval










namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_weightedRootIdentity_of_decoratedFormal
    (L : ℕ) [Fact (2 < L)]
    (hformal : ons_decoratedFormalKacWardIdentity L) :
    ons_weightedRootIdentity L := by
  intro a b weight q hq hweight hsmall
  have hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1 :=
    ons_card_mul_lt_one_of_Sherman_small q hsmall
  have hcardPos : 0 < Fintype.card (ons_Dart L) := Fintype.card_pos
  have hcardOne : (1 : ℝ) ≤ Fintype.card (ons_Dart L) := by
    exact_mod_cast hcardPos
  have hqOne : q ≤ 1 := by
    have hqCard : q ≤ (Fintype.card (ons_Dart L) : ℝ) * q := by
      nlinarith
    exact le_of_lt (hqCard.trans_lt hcard)
  let decWeight : ons_DecEdge L → ℂ := ons_decSpecializedWeight weight
  have hall : ∀ edge, ‖decWeight edge‖ ≤ 1 := by
    intro edge
    classical
    unfold decWeight ons_decSpecializedWeight
    split
    · exact (hweight _).trans hqOne
    · simp
  have hext : ∀ d,
      ‖decWeight s(d, ons_dartRev L d)‖ ≤ q := by
    intro d
    simpa only [decWeight, ons_decSpecializedWeight_external] using
      hweight (ons_portEdge L d)
  have hroot :=
    ons_detWalkRoot_eq_decoratedFullWeightedSpinSum_of_formal
      L hformal decWeight a b q hq hall hext hcard
  rw [ons_KWmatDecorationWeightedPhase_specialized,
    ons_decoratedFullWeightedSpinSum_specialized] at hroot
  exact hroot

theorem ons_spinKacWardIdentities_of_decoratedFormal
    (hformal : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_decoratedFormalKacWardIdentity L)
    (beta : ℝ) : ons_spinKacWardIdentities beta := by
  apply ons_spinKacWardIdentities_of_weightedRoot
  intro L hL
  letI : Fact (2 < L) := ⟨hL⟩
  exact ons_weightedRootIdentity_of_decoratedFormal L (hformal L hL)

end StatMech.Onsager
