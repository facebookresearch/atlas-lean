/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthSelectedOctadData

/-! Complete original real selected octad coordinates follow from the checked sparse source
  inverse. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem source_of_label (i : GeneratedAxisGlobalFifthShortPacketIndex)
    (s : Fin 11) (p : Fin 64)
    (hi : generatedAxisGlobalFifthRoot02ShortLabel i = Sum.inr (Sum.inl
        (generatedTenthSelectedShortOctad s, p))) :
    generatedTenthSelectedOctadSource ⟨64 * s.val + p.val, by omega⟩ =
      (generatedAxisGlobalFifthPacketNumber i).val := by
  have hn : generatedTenthIncomingShortLabel (generatedAxisGlobalFifthPacketNumber i) =
      Sum.inr (Sum.inl (generatedTenthSelectedShortOctad s, p)) := by
    change generatedAxisGlobalFifthRoot02ShortLabel i = _
    exact hi
  exact generatedTenth_selected_octad_source_forward
    (generatedAxisGlobalFifthPacketNumber i) s p hn

/-- The full actual incoming selected octad coefficient, including every original source and
  central sign. -/
theorem generatedTenth_incoming_selected_octad_coordinate (s : Fin 11) (p : Fin 64) :
    (griessConwayEncode (rhoLocal generatedTenthLocal generatedFifthAxis)).2.1 (Sum.inr (Sum.inl
        (generatedTenthSelectedShortOctad s, p))) =
      if h : generatedTenthSelectedOctadSource ⟨64 * s.val + p.val, by omega⟩ < 4136 then
        let i := generatedAxisGlobalFifthPacketFromNumber
          ⟨generatedTenthSelectedOctadSource ⟨64 * s.val + p.val, by omega⟩, h⟩
        generatedAxisGlobalFifthShortPacketCoefficient i *
          qSign (generatedAxisGlobalFifthRoot02ShortPhase i)
      else 0 := by
  rw [generatedTenthLocal, generatedAxisGlobalFifthRoot02Packet_actual]
  change (∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
      (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot02ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot02ShortLabel i) (1 : ℝ)) (Sum.inr (Sum.inl
            (generatedTenthSelectedShortOctad s, p))) = _
  rw [Finset.sum_apply]
  split_ifs with h
  · let n : Fin 4136 := ⟨generatedTenthSelectedOctadSource ⟨64 * s.val + p.val, by omega⟩, h⟩
    let j := generatedAxisGlobalFifthPacketFromNumber n
    have hj : generatedAxisGlobalFifthRoot02ShortLabel j = Sum.inr (Sum.inl
        (generatedTenthSelectedShortOctad s, p)) := by
      have hh := generatedTenth_selected_octad_source_reverse s p h
      change generatedTenthIncomingShortLabel n = _ at hh
      change generatedTenthIncomingShortLabel (generatedAxisGlobalFifthPacketNumber j) = _
      rw [generatedAxisGlobalFifthPacketNumber_fromNumber]
      exact hh
    rw [Finset.sum_eq_single j]
    · simp only [hj, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, j, n]
    · intro i _ hij
      have hi : generatedAxisGlobalFifthRoot02ShortLabel i ≠ Sum.inr (Sum.inl
          (generatedTenthSelectedShortOctad s, p)) := by
        intro hi
        have hp := source_of_label i s p hi
        have hn : generatedAxisGlobalFifthPacketNumber i = n := by
          apply Fin.ext
          exact hp.symm
        have he := congrArg generatedAxisGlobalFifthPacketFromNumber hn
        rw [generatedAxisGlobalFifthPacketFromNumber_number] at he
        exact hij he
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hi.symm, mul_zero]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    have hi : generatedAxisGlobalFifthRoot02ShortLabel i ≠ Sum.inr (Sum.inl
        (generatedTenthSelectedShortOctad s, p)) := by
      intro hi
      have hp := source_of_label i s p hi
      have hb := (generatedAxisGlobalFifthPacketNumber i).isLt
      apply h
      rw [hp]
      exact hb
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hi.symm, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
