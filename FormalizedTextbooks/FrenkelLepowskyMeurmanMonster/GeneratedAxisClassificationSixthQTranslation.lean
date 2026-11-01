/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorMaximum
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQFixedCriteria

/-! Genuine full-axis fixation forces zero translation and an even modulation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full original axis fixation preserves the denominator-cleared actual tensor column. -/
theorem generatedSixth_Q_tensor_column_fixed (q : Q)
    (hq : rhoLocal (inclQ q) generatedSixthAxis = generatedSixthAxis) :
    spinRepresentation q generatedSixthTensorColumn = generatedSixthTensorColumn := by
  have ht := ((generatedFourthQ_full_fixed_iff q generatedSixthAxis).mp hq).2 16
  change spinRepresentation q ((32 * Real.sqrt 2) •
    (fun t => (griessConwayEncode generatedSixthAxis).2.2 t 16)) = _
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
theorem generatedSixth_Q_translation_zero (q : Q)
    (hq : rhoLocal (inclQ q) generatedSixthAxis = generatedSixthAxis) :
    spinTranslation q = 0 := by
  obtain ⟨t, ht, hu⟩ := generatedSixth_tensor_unique_maximum
  have he := fixed_square q generatedSixthTensorColumn
    (generatedSixth_Q_tensor_column_fixed q hq) t
  have hz := hu (t + spinTranslation q) (he.trans ht)
  exact add_left_cancel (hz.trans (add_zero t).symm)

/-- Both actual exceptional Ω coordinates are nonzero. -/
theorem generatedSixth_tensor_exceptional_nonzero :
    generatedSixthTensorColumn (golayLabelCoefficients 1010) ≠ 0 ∧
      generatedSixthTensorColumn (golayLabelCoefficients 3058) ≠ 0 := by
  rcases generatedSixth_tensor_exceptional_squares with h | h
  all_goals constructor
  all_goals intro hz
  all_goals first
  | have he := h.1; rw [hz] at he; norm_num at he
  | have he := h.2; rw [hz] at he; norm_num at he

/-- The two nonzero Ω-related tensor coordinates force even genuine modulation. -/
theorem generatedSixth_Q_modulation_even (q : Q)
    (hq : rhoLocal (inclQ q) generatedSixthAxis = generatedSixthAxis) :
    spinModulation q 11 = 0 := by
  have ht := generatedSixth_Q_translation_zero q hq
  have he := generatedSpinSupport_fixed_modulation_difference q generatedSixthTensorColumn 0
    (generatedSixth_Q_tensor_column_fixed q hq)
    (fun t => by simp only [ht, add_zero, qSign_zero, one_mul])
    (golayLabelCoefficients 1010) (golayLabelCoefficients 3058)
    generatedSixth_tensor_exceptional_nonzero.1 generatedSixth_tensor_exceptional_nonzero.2
  have ho : golayLabelCoefficients 1010 + golayLabelCoefficients 3058 =
      Pi.single (11 : Fin 12) 1 := by
    have h := golayLabel_low_add_omega (1010 : Fin 2048)
    change golayLabelCoefficients 1010 + Pi.single (11 : Fin 12) 1 =
      golayLabelCoefficients 3058 at h
    rw [← h, ← add_assoc, ZModModule.add_self, zero_add]
  rw [ho] at he
  simpa only [spinDot, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
