/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Source x82 in Fourier tensor coordinates, needed for the remaining source-word rows. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82YRow

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The lower source code label obtained by the actual code-vector sum with e82. -/
noncomputable def monsterY82CodeSum (d : Fin 2048) : Fin 2048 :=
  spinDictionaryCode (golayLabelCoefficients ⟨d.val, by omega⟩ + monsterSourceY82Code)

/-- The code sum retains its genuine lower representative, with no all-one ambiguity. -/
theorem monsterY82CodeSum_low (d : Fin 2048) :
    golayLabelCoefficients ⟨(monsterY82CodeSum d).val, by omega⟩ =
      golayLabelCoefficients ⟨d.val, by omega⟩ + monsterSourceY82Code := by
  have hlast : (golayLabelCoefficients ⟨d.val, by omega⟩ + monsterSourceY82Code) 11 = 0 := by
    rw [Pi.add_apply, golayLabel_low_last, monsterSourceY82Code_last, zero_add]
  rcases spinDictionaryIndex_cases
    (golayLabelCoefficients ⟨d.val, by omega⟩ + monsterSourceY82Code) with h | h
  · exact h.symm
  · have hh := congrFun h 11
    rw [hlast, golayLabel_high_last] at hh
    exact False.elim (zero_ne_one hh)

/-- The upper representative of the same genuine sum has the identical code translation. -/
theorem monsterY82CodeSum_high (d : Fin 2048) :
    golayLabelCoefficients ⟨(monsterY82CodeSum d).val + 2048, by omega⟩ =
      golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + monsterSourceY82Code := by
  rw [← golayLabel_low_add_omega, monsterY82CodeSum_low, ← golayLabel_low_add_omega]
  abel

/-- The actual x82 code lift is fixed by the one-coordinate Fourier conjugation. -/
theorem monsterY82_hadamard_code :
    monsterSpinHadamardImage (sourceQCode 82 0) = sourceQCode 82 0 := by
  have ha : spinTranslation (sourceQCode 82 0) 11 = 0 := by
    rw [sourceQCode_translation]
    exact monsterSourceY82Code_last
  have hb : spinModulation (sourceQCode 82 0) 11 = 0 := by
    rw [sourceQCode_modulation, ← sourceWordTheta_eq_polynomial, sourceWordTheta_last]
  apply NormalizedCocycleExtension.Extension.ext
  · apply (qBase_eq_iff_spin_coordinates _ _).mpr
    constructor
    · rw [monsterSpinHadamardImage_translation, ha, hb, zero_add, zero_smul, add_zero]
    · rw [monsterSpinHadamardImage_modulation, ha, hb, zero_add, zero_smul, add_zero]
  · apply Multiplicative.toAdd.injective
    change toAdd (sourceQCode 82 0).coeff +
      spinTranslation (sourceQCode 82 0) 11 * spinModulation (sourceQCode 82 0) 11 = _
    rw [ha, zero_mul, add_zero]

/-- The actual source x82 lift has central coefficient zero. -/
theorem monsterY82_sourceCode_coeff : toAdd (sourceQCode 82 0).coeff = 0 := by
  decide +kernel

/-- Its spin phase at the upper label is the exact lower theta character. -/
theorem monsterY82_sourceCode_phase_high (d : Fin 2048) :
    spinPhase (sourceQCode 82 0) (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) =
      spinDot (sourceCodeThetaPolynomial monsterSourceY82Code)
        (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  rw [spinPhase, monsterY82_sourceCode_coeff, zero_add, sourceQCode_modulation,
    ← golayLabel_low_add_omega, spinDot_add_right]
  have h : spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients 82))
      (Pi.single 11 1) = 0 := by
    rw [← sourceWordTheta_eq_polynomial]
    exact sourceWordTheta_dot_omega 82
  rw [h, add_zero]
  rfl

/-- The actual x82 tensor column is unchanged by its Fourier transport. -/
theorem monsterY82_sourceCode_hadamard_tensor (x : GriessSpace) (t : SpinIndex) (i : Fin 24) :
    monsterSpinHadamard
      (fun u => (griessConwayEncode (rhoLocal (inclQ (sourceQCode 82 0)) x)).2.2 u i) t =
        spinRepresentation (sourceQCode 82 0)
          (monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)) t := by
  have hf : (fun u => (griessConwayEncode
      (rhoLocal (inclQ (sourceQCode 82 0)) x)).2.2 u i) =
        spinRepresentation (sourceQCode 82 0) (fun u => (griessConwayEncode x).2.2 u i) := by
    funext u
    rw [show rhoLocal (inclQ (sourceQCode 82 0)) =
      localGriessRepresentation (localFiberIncl (sourceQCode 82 0)) from rfl,
      localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    exact localTensorRepresentation_q (sourceQCode 82 0) (griessConwayEncode x).2.2 u i
  rw [hf, monsterSpinHadamard_intertwines, monsterY82_hadamard_code]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
