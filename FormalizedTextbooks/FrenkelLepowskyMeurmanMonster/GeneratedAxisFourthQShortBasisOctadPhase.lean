/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOctadData
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Each finite octad phase is exactly the actual preferred short conjugation phase. -/
theorem generatedFourthQShortBasis_octad_phase_actual (i : Fin 7) (j : Fin 63) (e : Fin 64) :
    Multiplicative.toAdd (localAxisQPhase
      (Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, e)))
      (generatedFourthQAffineParameterBasis i)) = generatedFourthQShortBasisOctadPhase i j e := by
  rw [generatedFourthQAffineParameterBasis_literal, generatedFourthQShortBasis_octad_character,
    generatedFourthEvenRootOctad_label]
  have hn : integerParity (griessOctadNegativeInteger (generatedFourthEvenRootOctad j) e) =
      (fun k : Fin 24 =>
        if (generatedFourthEvenOctadSignMask j e).testBit k.val then 1 else 0) := by
    funext k
    simp [integerParity, griessOctadNegativeInteger, generatedFourth_even_octad_sign_mask]
  rw [hn, spinDot_add_right
    (golayLabelCoefficients (generatedFourthQAffineParameterBasisModulationLabels i))
    (golayLabelCoefficients (generatedFourthEvenRootCode j))
    (griessOctadOmegaCoefficient e • Pi.single 11 1),
    generatedAxisFourthQAffineParameter_dot_smul_right]
  have hm : spinDot
      (golayLabelCoefficients (generatedFourthQAffineParameterBasisModulationLabels i))
      (Pi.single 11 1) = 0 := by
    simp [spinDot, Pi.single_apply, generatedFourthQShortBasis_modulation_last]
  simp only [hm, mul_zero, add_zero]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
