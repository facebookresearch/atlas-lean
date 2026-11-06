/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Fourier tensor dictionary for Norton's initial x400 point.
The proofs specialize the existing source-code/Fourier APIs also used for x82. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82ZRow
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsFirstLine

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual binary code vector of the initial Norton point x400. -/
def monsterNortonInitialCode : SpinIndex := golayLabelCoefficients 1024

/-- Its source representative is even. -/
theorem monsterNortonInitialCode_last : monsterNortonInitialCode 11 = 0 := by
  decide +kernel

/-- The lower source code label obtained by the actual code-vector sum with e400. -/
noncomputable def monsterNortonInitialCodeSum (d : Fin 2048) : Fin 2048 :=
  spinDictionaryCode (golayLabelCoefficients ⟨d.val, by omega⟩ + monsterNortonInitialCode)

/-- The code sum retains its genuine lower representative, with no all-one ambiguity. -/
theorem monsterNortonInitialCodeSum_low (d : Fin 2048) :
    golayLabelCoefficients ⟨(monsterNortonInitialCodeSum d).val, by omega⟩ =
      golayLabelCoefficients ⟨d.val, by omega⟩ + monsterNortonInitialCode := by
  have hlast : (golayLabelCoefficients ⟨d.val, by omega⟩ + monsterNortonInitialCode) 11 = 0 := by
    rw [Pi.add_apply, golayLabel_low_last, monsterNortonInitialCode_last, zero_add]
  rcases spinDictionaryIndex_cases
    (golayLabelCoefficients ⟨d.val, by omega⟩ + monsterNortonInitialCode) with h | h
  · exact h.symm
  · have hh := congrFun h 11
    rw [hlast, golayLabel_high_last] at hh
    exact False.elim (zero_ne_one hh)

/-- The upper representative of the same genuine sum has the identical code translation. -/
theorem monsterNortonInitialCodeSum_high (d : Fin 2048) :
    golayLabelCoefficients ⟨(monsterNortonInitialCodeSum d).val + 2048, by omega⟩ =
      golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + monsterNortonInitialCode := by
  rw [← golayLabel_low_add_omega, monsterNortonInitialCodeSum_low, ← golayLabel_low_add_omega]
  abel

/-- The actual x400 code lift is fixed by the one-coordinate Fourier conjugation. -/
theorem monsterNortonInitial_hadamard_code :
    monsterSpinHadamardImage (sourceQCode 1024 0) = sourceQCode 1024 0 := by
  have ha : spinTranslation (sourceQCode 1024 0) 11 = 0 := by
    rw [sourceQCode_translation]
    exact monsterNortonInitialCode_last
  have hb : spinModulation (sourceQCode 1024 0) 11 = 0 := by
    rw [sourceQCode_modulation, ← sourceWordTheta_eq_polynomial, sourceWordTheta_last]
  apply NormalizedCocycleExtension.Extension.ext
  · apply (qBase_eq_iff_spin_coordinates _ _).mpr
    constructor
    · rw [monsterSpinHadamardImage_translation, ha, hb, zero_add, zero_smul, add_zero]
    · rw [monsterSpinHadamardImage_modulation, ha, hb, zero_add, zero_smul, add_zero]
  · apply Multiplicative.toAdd.injective
    change toAdd (sourceQCode 1024 0).coeff +
      spinTranslation (sourceQCode 1024 0) 11 * spinModulation (sourceQCode 1024 0) 11 = _
    rw [ha, zero_mul, add_zero]

/-- The actual source x400 lift has central coefficient zero. -/
theorem monsterNortonInitial_sourceCode_coeff : toAdd (sourceQCode 1024 0).coeff = 0 := by
  decide +kernel

/-- Its spin phase at the upper label is the exact lower theta character. -/
theorem monsterNortonInitial_sourceCode_phase_high (d : Fin 2048) :
    spinPhase (sourceQCode 1024 0)
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) =
      spinDot
        (sourceCodeThetaPolynomial monsterNortonInitialCode)
        (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  rw [spinPhase, monsterNortonInitial_sourceCode_coeff, zero_add, sourceQCode_modulation,
    ← golayLabel_low_add_omega, spinDot_add_right]
  have h : spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients 1024))
      (Pi.single 11 1) = 0 := by
    rw [← sourceWordTheta_eq_polynomial]
    exact sourceWordTheta_dot_omega 1024
  rw [h, add_zero]
  rfl

/-- The actual x400 tensor column is unchanged by its Fourier transport. -/
theorem monsterNortonInitial_sourceCode_hadamard_tensor (x : GriessSpace)
    (t : SpinIndex) (i : Fin 24) :
    monsterSpinHadamard
      (fun u => (griessConwayEncode (rhoLocal (inclQ (sourceQCode 1024 0)) x)).2.2 u i) t =
        spinRepresentation (sourceQCode 1024 0)
          (monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)) t := by
  have hf : (fun u => (griessConwayEncode
      (rhoLocal (inclQ (sourceQCode 1024 0)) x)).2.2 u i) =
        spinRepresentation (sourceQCode 1024 0) (fun u => (griessConwayEncode x).2.2 u i) := by
    funext u
    rw [show rhoLocal (inclQ (sourceQCode 1024 0)) =
      localGriessRepresentation (localFiberIncl (sourceQCode 1024 0)) from rfl,
      localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    exact localTensorRepresentation_q (sourceQCode 1024 0) (griessConwayEncode x).2.2 u i
  rw [hf, monsterSpinHadamard_intertwines, monsterNortonInitial_hadamard_code]

/-- The source x400 code action on Y has its exact theta and physical-coordinate signs. -/
theorem monsterNortonInitial_sourceCode_blocks_Y (x : GriessSpace)
    (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode 1024 0)) x)).2.2.2 1
      (finProdFinEquiv (d,i)) =
        qSign (golayEncoder monsterNortonInitialCode i) *
          qSign (spinDot
        (sourceCodeThetaPolynomial monsterNortonInitialCode)
            (golayLabelCoefficients ⟨d.val, by omega⟩)) *
              (trialityBlocksEquiv x).2.2.2 1
                (finProdFinEquiv (monsterNortonInitialCodeSum d,i)) := by
  have h := monsterNortonInitial_sourceCode_hadamard_tensor x
    (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i
  rw [monsterY82_hadamard_encode_high, monsterMonomialSpinRepresentation_apply,
    monsterNortonInitial_sourceCode_phase_high, sourceQCode_translation] at h
  change _ = qSign (spinDot
        (sourceCodeThetaPolynomial monsterNortonInitialCode)
      (golayLabelCoefficients ⟨d.val, by omega⟩)) *
    monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + monsterNortonInitialCode) at h
  rw [← monsterNortonInitialCodeSum_high, monsterY82_hadamard_encode_high,
    ← golayEncoder_low_qSign, ← golayEncoder_low_qSign, monsterNortonInitialCodeSum_low,
    map_add, Pi.add_apply, qSign_add] at h
  have hsq := qSign_sq (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i)
  calc
    _ = qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
        (qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
          (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode 1024 0)) x)).2.2.2 1
            (finProdFinEquiv (d,i))) := by rw [← mul_assoc, hsq, one_mul]
    _ = (qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
        qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i)) *
          (qSign (golayEncoder monsterNortonInitialCode i) *
            qSign (spinDot
        (sourceCodeThetaPolynomial monsterNortonInitialCode)
              (golayLabelCoefficients ⟨d.val, by omega⟩)) *
                (trialityBlocksEquiv x).2.2.2 1
                  (finProdFinEquiv (monsterNortonInitialCodeSum d,i))) := by rw [h]; ring
    _ = _ := by rw [hsq, one_mul]

/-- The lower-label spin phase is the same actual theta character. -/
theorem monsterNortonInitial_sourceCode_phase_low (d : Fin 2048) :
    spinPhase (sourceQCode 1024 0) (golayLabelCoefficients ⟨d.val, by omega⟩) =
      spinDot
        (sourceCodeThetaPolynomial monsterNortonInitialCode)
        (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  rw [spinPhase, monsterNortonInitial_sourceCode_coeff, zero_add, sourceQCode_modulation]
  rfl

/-- The actual x400 Z row has its complete quarter-weight and theta signs. -/
theorem monsterNortonInitial_sourceCode_blocks_Z (x : GriessSpace)
    (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode 1024 0)) x)).2.2.2 2
      (finProdFinEquiv (d,i)) =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        qSign (spinDot
        (sourceCodeThetaPolynomial monsterNortonInitialCode)
          (golayLabelCoefficients ⟨d.val, by omega⟩)) *
        qSign (golayMaskWeight (golayEncodedMask (monsterNortonInitialCodeSum d).val) / 4 : ℕ)) *
          (trialityBlocksEquiv x).2.2.2 2
            (finProdFinEquiv (monsterNortonInitialCodeSum d,i)) := by
  have h := monsterNortonInitial_sourceCode_hadamard_tensor x
    (golayLabelCoefficients ⟨d.val, by omega⟩) i
  rw [monsterY82_hadamard_encode_low, monsterMonomialSpinRepresentation_apply,
    monsterNortonInitial_sourceCode_phase_low, sourceQCode_translation] at h
  change _ = qSign (spinDot
        (sourceCodeThetaPolynomial monsterNortonInitialCode)
      (golayLabelCoefficients ⟨d.val, by omega⟩)) *
    monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)
      (golayLabelCoefficients ⟨d.val, by omega⟩ + monsterNortonInitialCode) at h
  rw [← monsterNortonInitialCodeSum_low, monsterY82_hadamard_encode_low] at h
  have hsq := qSign_sq (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  calc
    _ = qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode 1024 0)) x)).2.2.2 2
            (finProdFinEquiv (d,i))) := by rw [← mul_assoc, hsq, one_mul]
    _ = _ := by rw [h]; ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
