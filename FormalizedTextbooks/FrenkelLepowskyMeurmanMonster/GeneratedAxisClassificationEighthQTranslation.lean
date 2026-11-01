/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQHighSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQColumn

/-! Full-axis fixation preserves the genuine high support and its unequal omega-pair squares. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every full-axis fixer translates the actual high support by zero or omega. -/
theorem generatedEighth_Q_translation_alternative (q : Q)
    (hq : q ∈ generatedEighthAxisQStabilizer) :
    spinTranslation q = 0 ∨ spinTranslation q = Pi.single (11 : Fin 12) 1 := by
  apply generatedEighth_high_spin_period
  intro t ht
  apply (generatedEighth_tensor_high_support _).mp
  rw [generatedEighth_Q_column_square q hq t]
  exact (generatedEighth_tensor_high_support t).mpr ht

/-- The actual unequal high-pair squares exclude omega, forcing zero Q translation. -/
theorem generatedEighth_Q_translation_zero (q : Q)
    (hq : q ∈ generatedEighthAxisQStabilizer) : spinTranslation q = 0 := by
  rcases generatedEighth_Q_translation_alternative q hq with ha | ha
  · exact ha
  · have hc : spinDictionaryCode (0 : SpinIndex) = generatedEighthHighOddCode (8 : Fin 12) := by
      have hz : golayLabelCoefficients
          ⟨(generatedEighthHighOddCode (8 : Fin 12)).val, by omega⟩ = 0 := by
        decide +kernel
      simpa only [hz] using spinDictionaryCode_low (generatedEighthHighOddCode (8 : Fin 12))
    have hs := generatedEighth_Q_column_square q hq 0
    rw [ha, zero_add] at hs
    rcases generatedEighth_tensor_high_pair_squares 8 0 hc with h | h
    · rw [zero_add] at h
      rw [h.1, h.2] at hs
      norm_num at hs
    · rw [zero_add] at h
      rw [h.1, h.2] at hs
      norm_num at hs

/-- Every actual Q element fixing the full Eighth axis is the identity. -/
theorem generatedEighth_Q_fixed_eq_one (q : Q)
    (hq : q ∈ generatedEighthAxisQStabilizer) : q = 1 :=
  generatedEighth_Q_eq_one_of_translation_zero q hq (generatedEighth_Q_translation_zero q hq)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
