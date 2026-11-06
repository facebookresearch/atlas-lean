/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Fourier tensor dictionary for arbitrary even source codes with quarter-weight parity zero.
The proofs specialize the existing source-code/Fourier APIs also used for x82. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82ZRow

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
variable (a : Fin 2048)
variable (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0)

/-- The actual binary code vector of the initial Norton point x400. -/
def monsterNortonEvenCodeVector : SpinIndex := golayLabelCoefficients ⟨a.val, by omega⟩

/-- Its source representative is even. -/
theorem monsterNortonEvenCodeVector_last : (monsterNortonEvenCodeVector a) 11 = 0 := by
  exact golayLabel_low_last a

/-- The lower source code label obtained by the actual code-vector sum with the given code. -/
noncomputable def monsterNortonEvenCodeSum (d : Fin 2048) : Fin 2048 :=
  spinDictionaryCode (golayLabelCoefficients ⟨d.val, by omega⟩ + (monsterNortonEvenCodeVector a))

/-- The code sum retains its genuine lower representative, with no all-one ambiguity. -/
theorem monsterNortonEvenCodeSum_low (d : Fin 2048) :
    golayLabelCoefficients ⟨((monsterNortonEvenCodeSum a) d).val, by omega⟩ =
      golayLabelCoefficients ⟨d.val, by omega⟩ + (monsterNortonEvenCodeVector a) := by
  have hlast : (golayLabelCoefficients ⟨d.val, by omega⟩ + (monsterNortonEvenCodeVector a)) 11 =
    0 := by
    rw [Pi.add_apply, golayLabel_low_last, (monsterNortonEvenCodeVector_last a), zero_add]
  rcases spinDictionaryIndex_cases
    (golayLabelCoefficients ⟨d.val, by omega⟩ + (monsterNortonEvenCodeVector a)) with h | h
  · exact h.symm
  · have hh := congrFun h 11
    rw [hlast, golayLabel_high_last] at hh
    exact False.elim (zero_ne_one hh)

/-- The upper representative of the same genuine sum has the identical code translation. -/
theorem monsterNortonEvenCodeSum_high (d : Fin 2048) :
    golayLabelCoefficients ⟨((monsterNortonEvenCodeSum a) d).val + 2048, by omega⟩ =
      golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + (monsterNortonEvenCodeVector a) := by
  rw [← golayLabel_low_add_omega, (monsterNortonEvenCodeSum_low a), ← golayLabel_low_add_omega]
  abel

/-- The actual x400 code lift is fixed by the one-coordinate Fourier conjugation. -/
theorem monsterNortonEven_hadamard_code :
    monsterSpinHadamardImage (sourceQCode ⟨a.val, by omega⟩ 0) = sourceQCode ⟨a.val, by omega⟩ 0
      := by
  have ha : spinTranslation (sourceQCode ⟨a.val, by omega⟩ 0) 11 = 0 := by
    rw [sourceQCode_translation]
    exact (monsterNortonEvenCodeVector_last a)
  have hb : spinModulation (sourceQCode ⟨a.val, by omega⟩ 0) 11 = 0 := by
    rw [sourceQCode_modulation, ← sourceWordTheta_eq_polynomial, sourceWordTheta_last]
  apply NormalizedCocycleExtension.Extension.ext
  · apply (qBase_eq_iff_spin_coordinates _ _).mpr
    constructor
    · rw [monsterSpinHadamardImage_translation, ha, hb, zero_add, zero_smul, add_zero]
    · rw [monsterSpinHadamardImage_modulation, ha, hb, zero_add, zero_smul, add_zero]
  · apply Multiplicative.toAdd.injective
    change toAdd (sourceQCode ⟨a.val, by omega⟩ 0).coeff +
      spinTranslation (sourceQCode ⟨a.val, by omega⟩ 0) 11 * spinModulation (sourceQCode ⟨a.val,
        by omega⟩ 0) 11 = _
    rw [ha, zero_mul, add_zero]

/-- The actual source code lift has central coefficient zero. -/
theorem monsterNortonEven_sourceCode_coeff
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) : toAdd
      (sourceQCode ⟨a.val, by omega⟩ 0).coeff = 0 := by
  change (0 : ZMod 2) + (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) = 0
  simpa only [zero_add] using ha

/-- Its spin phase at the upper label is the exact lower theta character. -/
theorem monsterNortonEven_sourceCode_phase_high
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (d : Fin 2048) :
    spinPhase (sourceQCode ⟨a.val, by omega⟩ 0)
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) =
      spinDot
        (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
        (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  rw [spinPhase, (monsterNortonEven_sourceCode_coeff a ha), zero_add, sourceQCode_modulation,
    ← golayLabel_low_add_omega, spinDot_add_right]
  have h : spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients ⟨a.val, by omega⟩))
      (Pi.single 11 1) = 0 := by
    rw [← sourceWordTheta_eq_polynomial]
    exact sourceWordTheta_dot_omega ⟨a.val, by omega⟩
  rw [h, add_zero]
  rfl

/-- The actual x400 tensor column is unchanged by its Fourier transport. -/
theorem monsterNortonEven_sourceCode_hadamard_tensor (x : GriessSpace)
    (t : SpinIndex) (i : Fin 24) :
    monsterSpinHadamard
      (fun u => (griessConwayEncode (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) x)).2.2
        u i) t =
        spinRepresentation (sourceQCode ⟨a.val, by omega⟩ 0)
          (monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)) t := by
  have hf : (fun u => (griessConwayEncode
      (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) x)).2.2 u i) =
        spinRepresentation (sourceQCode ⟨a.val, by omega⟩ 0) (fun u => (griessConwayEncode
          x).2.2 u i) := by
    funext u
    rw [show rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) =
      localGriessRepresentation (localFiberIncl (sourceQCode ⟨a.val, by omega⟩ 0)) from rfl,
      localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    exact localTensorRepresentation_q (sourceQCode ⟨a.val, by omega⟩ 0) (griessConwayEncode
      x).2.2 u i
  rw [hf, monsterSpinHadamard_intertwines, (monsterNortonEven_hadamard_code a)]

/-- The source code code action on Y has its exact theta and physical-coordinate signs. -/
theorem monsterNortonEven_sourceCode_blocks_Y
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (x : GriessSpace)
    (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) x)).2.2.2 1
      (finProdFinEquiv (d,i)) =
        qSign (golayEncoder (monsterNortonEvenCodeVector a) i) *
          qSign (spinDot
        (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
            (golayLabelCoefficients ⟨d.val, by omega⟩)) *
              (trialityBlocksEquiv x).2.2.2 1
                (finProdFinEquiv ((monsterNortonEvenCodeSum a) d,i)) := by
  have h := (monsterNortonEven_sourceCode_hadamard_tensor a) x
    (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i
  rw [monsterY82_hadamard_encode_high, monsterMonomialSpinRepresentation_apply,
    (monsterNortonEven_sourceCode_phase_high a ha), sourceQCode_translation] at h
  change _ = qSign (spinDot
        (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
      (golayLabelCoefficients ⟨d.val, by omega⟩)) *
    monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + (monsterNortonEvenCodeVector a)) at h
  rw [← (monsterNortonEvenCodeSum_high a), monsterY82_hadamard_encode_high,
    ← golayEncoder_low_qSign, ← golayEncoder_low_qSign, (monsterNortonEvenCodeSum_low a),
    map_add, Pi.add_apply, qSign_add] at h
  have hsq := qSign_sq (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i)
  calc
    _ = qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
        (qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
          (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) x)).2.2.2 1
            (finProdFinEquiv (d,i))) := by rw [← mul_assoc, hsq, one_mul]
    _ = (qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
        qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i)) *
          (qSign (golayEncoder (monsterNortonEvenCodeVector a) i) *
            qSign (spinDot
        (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
              (golayLabelCoefficients ⟨d.val, by omega⟩)) *
                (trialityBlocksEquiv x).2.2.2 1
                  (finProdFinEquiv ((monsterNortonEvenCodeSum a) d,i))) := by rw [h]; ring
    _ = _ := by rw [hsq, one_mul]

/-- The lower-label spin phase is the same actual theta character. -/
theorem monsterNortonEven_sourceCode_phase_low
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (d : Fin 2048) :
    spinPhase (sourceQCode ⟨a.val, by omega⟩ 0) (golayLabelCoefficients ⟨d.val, by omega⟩) =
      spinDot
        (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
        (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  rw [spinPhase, (monsterNortonEven_sourceCode_coeff a ha), zero_add, sourceQCode_modulation]
  rfl

/-- The actual x400 Z row has its complete quarter-weight and theta signs. -/
theorem monsterNortonEven_sourceCode_blocks_Z
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (x : GriessSpace)
    (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) x)).2.2.2 2
      (finProdFinEquiv (d,i)) =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        qSign (spinDot
        (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
          (golayLabelCoefficients ⟨d.val, by omega⟩)) *
        qSign (golayMaskWeight (golayEncodedMask ((monsterNortonEvenCodeSum a) d).val) / 4 : ℕ)) *
          (trialityBlocksEquiv x).2.2.2 2
            (finProdFinEquiv ((monsterNortonEvenCodeSum a) d,i)) := by
  have h := (monsterNortonEven_sourceCode_hadamard_tensor a) x
    (golayLabelCoefficients ⟨d.val, by omega⟩) i
  rw [monsterY82_hadamard_encode_low, monsterMonomialSpinRepresentation_apply,
    (monsterNortonEven_sourceCode_phase_low a ha), sourceQCode_translation] at h
  change _ = qSign (spinDot
        (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
      (golayLabelCoefficients ⟨d.val, by omega⟩)) *
    monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)
      (golayLabelCoefficients ⟨d.val, by omega⟩ + (monsterNortonEvenCodeVector a)) at h
  rw [← (monsterNortonEvenCodeSum_low a), monsterY82_hadamard_encode_low] at h
  have hsq := qSign_sq (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  calc
    _ = qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) x)).2.2.2 2
            (finProdFinEquiv (d,i))) := by rw [← mul_assoc, hsq, one_mul]
    _ = _ := by rw [h]; ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
