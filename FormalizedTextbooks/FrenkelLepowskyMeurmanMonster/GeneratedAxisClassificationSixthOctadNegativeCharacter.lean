/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthOctadSignCharacter

/-! The genuine preferred octad cocode carries the original six-bit sign character. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original negative-position vector is the sum of its eight distinct local indicators. -/
theorem generatedSixth_octad_negative_indicator (o : Fin 759) (e : Fin 64) (i : Fin 24) :
    integerParity (griessOctadNegativeInteger o e) i =
      ∑ a : Fin 8, if golayOctadCoordinate o a = i then
        (if (trialityEvenMask e).testBit a.val then (1 : ZMod 2) else 0) else 0 := by
  change (griessOctadNegativeInteger o e i : ZMod 2) = _
  by_cases hi : ∃ a : Fin 8, golayOctadCoordinate o a = i
  · obtain ⟨a, rfl⟩ := hi
    have hm : (griessOctadSignMask o e).testBit (golayOctadCoordinate o a).val = true ↔
        (trialityEvenMask e).testBit a.val = true := by
      rw [griessOctadSignMask_testBit]
      constructor
      · rintro ⟨b, hb, hab⟩
        have hba := golayOctadCoordinate_injective o hab
        simpa only [hba] using hb
      · intro ha
        exact ⟨a, ha, rfl⟩
    rw [Finset.sum_eq_single a]
    · simp only [griessOctadNegativeInteger,
        ite_true, Int.cast_ite, Int.cast_one, Int.cast_zero]
      by_cases ha : (trialityEvenMask e).testBit a.val = true
      · simp only [ha, hm.mpr ha, ite_true]
      · have hn : (griessOctadSignMask o e).testBit
            (golayOctadCoordinate o a).val ≠ true := fun h => ha (hm.mp h)
        simp only [ha, hn]
    · intro b _ hba
      simp only [ite_eq_right_iff]
      intro h
      exact False.elim (hba (golayOctadCoordinate_injective o h))
    · intro ha
      exact False.elim (ha (Finset.mem_univ _))
  · have hm : (griessOctadSignMask o e).testBit i.val ≠ true := by
      intro h
      obtain ⟨a, _, ha⟩ := (griessOctadSignMask_testBit o e i).mp h
      exact hi ⟨a, ha⟩
    simp only [griessOctadNegativeInteger, hm]
    symm
    apply Finset.sum_eq_zero
    intro a _
    simp only [ite_eq_right_iff]
    intro h
    exact False.elim (hi ⟨a, h⟩)

/-- A cocode dot evaluates the genuine negative positions at the eight octad coordinates. -/
theorem generatedSixth_octad_negative_dot (u : SpinIndex) (o : Fin 759) (e : Fin 64) :
    spinDot u (golaySyndrome (integerParity (griessOctadNegativeInteger o e))) =
      ∑ a : Fin 8, golayEncoder u (golayOctadCoordinate o a) *
        (if (trialityEvenMask e).testBit a.val then 1 else 0) := by
  rw [generatedSixth_golay_syndrome_dot]
  simp_rw [generatedSixth_octad_negative_indicator, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The actual preferred octad negative cocode is a six-coordinate binary character. -/
theorem generatedSixth_octad_negative_character (u : SpinIndex) (o : Fin 759) (e : Fin 64) :
    spinDot u (golaySyndrome (integerParity (griessOctadNegativeInteger o e))) =
      ∑ a : Fin 6,
        (golayEncoder u (golayOctadCoordinate o (Fin.castAdd 2 a)) +
          golayEncoder u (golayOctadCoordinate o 6)) *
        (if e.val.testBit a.val then 1 else 0) := by
  rw [generatedSixth_octad_negative_dot]
  exact generatedSixth_octad_sign_character _ e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
