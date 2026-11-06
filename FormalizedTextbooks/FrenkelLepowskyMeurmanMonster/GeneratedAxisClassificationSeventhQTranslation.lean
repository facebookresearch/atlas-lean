/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhTensorMaximum
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQFixedCriteria

/-! Genuine full-axis fixation forces zero translation and an even modulation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full original axis fixation preserves the denominator-cleared actual tensor column. -/
theorem generatedSeventh_Q_tensor_column_fixed (q : Q)
    (hq : rhoLocal (inclQ q) generatedSeventhAxis = generatedSeventhAxis) :
    spinRepresentation q generatedSeventhTensorColumn = generatedSeventhTensorColumn := by
  have ht := ((generatedFourthQ_full_fixed_iff q generatedSeventhAxis).mp hq).2 16
  change spinRepresentation q ((32 * Real.sqrt 2) •
    (fun t => (griessConwayEncode generatedSeventhAxis).2.2 t 16)) = _
  rw [map_smul, ht]
  rfl

private theorem fixed_square (q : Q) (f : SpinSpace)
    (hf : spinRepresentation q f = f) (t : SpinIndex) :
    (f (t + spinTranslation q)) ^ 2 = (f t) ^ 2 := by
  have h := (generatedSpinSupport_fixed_iff q f).mp hf t
  have hs := congrArg (fun z : ℝ => z ^ 2) h
  rw [mul_pow] at hs
  have hsign : (qSign (spinPhase q t)) ^ 2 = 1 := by rw [pow_two, qSign_sq]
  rw [hsign, one_mul] at hs
  exact hs

/-- The unique actual tensor maximum excludes every nonzero extraspecial translation. -/
theorem generatedSeventh_Q_translation_zero (q : Q)
    (hq : rhoLocal (inclQ q) generatedSeventhAxis = generatedSeventhAxis) :
    spinTranslation q = 0 := by
  obtain ⟨t, ht, hu⟩ := generatedSeventh_tensor_unique_maximum
  have he := fixed_square q generatedSeventhTensorColumn
    (generatedSeventh_Q_tensor_column_fixed q hq) t
  have hz := hu (t + spinTranslation q) (he.trans ht)
  exact add_left_cancel (hz.trans (add_zero t).symm)

/-- Both actual exceptional Ω coordinates are nonzero. -/
theorem generatedSeventh_tensor_exceptional_nonzero :
    generatedSeventhTensorColumn (golayLabelCoefficients 1012) ≠ 0 ∧
      generatedSeventhTensorColumn (golayLabelCoefficients 3060) ≠ 0 := by
  rcases generatedSeventh_tensor_exceptional_squares with h | h
  all_goals constructor
  all_goals intro hz
  all_goals first
  | have he := h.1; rw [hz] at he; norm_num at he
  | have he := h.2; rw [hz] at he; norm_num at he

/-- The two nonzero Ω-related tensor coordinates force even genuine modulation. -/
theorem generatedSeventh_Q_modulation_even (q : Q)
    (hq : rhoLocal (inclQ q) generatedSeventhAxis = generatedSeventhAxis) :
    spinModulation q 11 = 0 := by
  have ht := generatedSeventh_Q_translation_zero q hq
  have he := generatedSpinSupport_fixed_modulation_difference q generatedSeventhTensorColumn 0
    (generatedSeventh_Q_tensor_column_fixed q hq)
    (fun t => by simp only [ht, add_zero, qSign_zero, one_mul])
    (golayLabelCoefficients 1012) (golayLabelCoefficients 3060)
    generatedSeventh_tensor_exceptional_nonzero.1 generatedSeventh_tensor_exceptional_nonzero.2
  have ho : golayLabelCoefficients 1012 + golayLabelCoefficients 3060 =
      Pi.single (11 : Fin 12) 1 := by
    have h := golayLabel_low_add_omega (1012 : Fin 2048)
    change golayLabelCoefficients 1012 + Pi.single (11 : Fin 12) 1 =
      golayLabelCoefficients 3060 at h
    rw [← h, ← add_assoc, ZModModule.add_self, zero_add]
  rw [ho] at he
  simpa only [spinDot, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
