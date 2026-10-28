/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignSpin
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignFourier
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYAllTensor

/-! Actual Parker phase cancellations for every low original source sign, including odd quarters. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual full source label of a low sign code. -/
def generatedAxisGlobalSignLowCode (a : Fin 2048) : Fin 4096 := ⟨a.val, by omega⟩

/-- Every displayed low source dictionary row has last coordinate zero. -/
theorem generatedAxisGlobalSignLow_last (e : Fin 2048) : generatedFifthSpinLow e 11 = 0 :=
  golayLabel_low_last e

/-- Its actual code addition is precisely the displayed low dictionary relabeling. -/
theorem generatedAxisGlobalSignLow_translation (a e : Fin 2048) :
    generatedFifthSpinLow e + golayLabelCoefficients (generatedAxisGlobalSignLowCode a) =
      generatedFifthSpinLow (monsterNortonEvenCodeSum a e) :=
  (monsterNortonEvenCodeSum_low a e).symm

/-- Every quarter-weight contribution cancels to the prescribed upper Fourier character. -/
theorem generatedAxisGlobalSignLow_YPhase (a e : Fin 2048) :
    generatedAxisGlobalSignYPhase (generatedAxisGlobalSignLowCode a) 0
      (monsterNortonEvenCodeSum a e) e =
        spinDot (sourceCodeThetaPolynomial (generatedFifthSpinLow e)) (monsterNortonYCode a) :=
  by
    have h := monsterNortonYAll_phase a e
    rw [sourceWordTheta_polynomial, sourceWordTheta_polynomial] at h
    change (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) +
      (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) +
        spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) (generatedFifthSpinLow e) =
      spinDot (sourceCodeThetaPolynomial (generatedFifthSpinLow e)) (monsterNortonYCode a) +
        (golayMaskWeight (golayEncodedMask (monsterNortonEvenCodeSum a e).val) / 4 : ℕ) at h
    unfold generatedAxisGlobalSignYPhase
    rw [sourceWordTheta_polynomial]
    change ((0 : ZMod 2) + (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ)) +
      spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) (generatedFifthSpinLow e) +
        (golayMaskWeight (golayEncodedMask (monsterNortonEvenCodeSum a e).val) / 4 : ℕ) +
          (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) = _
    linear_combination (norm := skip) h
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero]

/-- The complete lower source phase is its physical sign and symmetric theta character. -/
theorem generatedAxisGlobalSignLow_ZPhase (a e : Fin 2048) (i : Fin 24) :
    qSign (generatedAxisGlobalSignZPhase (generatedAxisGlobalSignLowCode a) e i) =
      qSign (golayEncoder (monsterNortonYCode a) i) *
        qSign (spinDot (sourceCodeThetaPolynomial (generatedFifthSpinLow e))
          (monsterNortonYCode a) +
          spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) (generatedFifthSpinLow e)) :=
  by
    unfold generatedAxisGlobalSignZPhase
    rw [sourceWordTheta_polynomial, sourceWordTheta_polynomial]
    change qSign (spinDot (monsterNortonYCode a)
      (sourceCodeThetaPolynomial (generatedFifthSpinLow e)) +
        golayEncoder (monsterNortonYCode a) i +
          spinDot (generatedFifthSpinLow e) (sourceCodeThetaPolynomial (monsterNortonYCode a))) = _
    rw [spinDot_comm (monsterNortonYCode a), spinDot_comm (generatedFifthSpinLow e)]
    simp only [qSign_add]
    ring

/-- The two literal physical dictionary signs multiply to the genuine sign code. -/
theorem generatedAxisGlobalSignLow_code_signs (a e : Fin 2048) (i : Fin 24) :
    (if (golayEncodedMask e.val).testBit i.val then (-1 : ℝ) else 1) *
      (if (golayEncodedMask (monsterNortonEvenCodeSum a e).val).testBit i.val then -1 else 1) =
        qSign (golayEncoder (monsterNortonYCode a) i) := by
  rw [← golayEncoder_low_qSign, ← golayEncoder_low_qSign]
  have h : golayEncoder (generatedFifthSpinLow (monsterNortonEvenCodeSum a e)) i =
      golayEncoder (generatedFifthSpinLow e) i + golayEncoder (monsterNortonYCode a) i := by
    have h := congrArg (fun t => golayEncoder t i) (generatedAxisGlobalSignLow_translation a e)
    simp only [map_add, Pi.add_apply] at h
    exact h.symm
  change qSign (golayEncoder (generatedFifthSpinLow e) i) *
    qSign (golayEncoder (generatedFifthSpinLow (monsterNortonEvenCodeSum a e)) i) = _
  rw [h, qSign_add, ← mul_assoc, qSign_sq, one_mul]

/-- The lower row of the prescribed Fourier spin operator has exactly the actual source phase. -/
theorem generatedAxisGlobalSignPlusMinus_low (a e : Fin 2048) (f : SpinSpace) :
    (generatedAxisGlobalSignPlusMinus a).val f (generatedFifthSpinLow e) =
      qSign (spinDot (sourceCodeThetaPolynomial (generatedFifthSpinLow e)) (monsterNortonYCode a) +
        spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) (generatedFifthSpinLow e)) *
          f (generatedFifthSpinLow e) := by
  rw [generatedAxisGlobalSignPlusMinus_apply]
  simp only [generatedAxisGlobalSignLow_last, add_zero, one_mul, zero_smul]

/-- The upper row has exactly its actual theta character and original source relabeling. -/
theorem generatedAxisGlobalSignPlusMinus_high (a e : Fin 2048) (f : SpinSpace) :
    (generatedAxisGlobalSignPlusMinus a).val f
      (generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex)) =
        qSign (spinDot (sourceCodeThetaPolynomial (generatedFifthSpinLow e))
          (monsterNortonYCode a)) *
          f (generatedFifthSpinLow (monsterNortonEvenCodeSum a e) + (Pi.single 11 1 : SpinIndex)) :=
  by
    rw [generatedAxisGlobalSignPlusMinus_apply, sourceCodeThetaPolynomial_add_omega]
    have hl : (generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex)) 11 = 1 := by
      simp only [Pi.add_apply, generatedAxisGlobalSignLow_last, Pi.single_eq_same, zero_add]
    rw [hl, CharTwo.add_self_eq_zero, zero_mul, add_zero, one_smul]
    have he := generatedAxisGlobalSignLow_translation a e
    change generatedFifthSpinLow e + monsterNortonYCode a =
      generatedFifthSpinLow (monsterNortonEvenCodeSum a e) at he
    rw [add_right_comm, he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
