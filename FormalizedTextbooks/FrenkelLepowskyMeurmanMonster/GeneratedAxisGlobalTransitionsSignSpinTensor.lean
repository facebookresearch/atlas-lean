/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignFourierPhases

/-! Bind the complete prescribed spin operator to the actual original low source
sign tensor action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem actual_fourier_low (a e : Fin 2048)
    (T : SpinIndex → Fin 24 → ℝ) (i : Fin 24) :
    monsterSpinHadamard (fun t =>
      localTensorRepresentation
        (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0) T t i)
        (generatedFifthSpinLow e) =
      qSign (golayEncoder (monsterNortonYCode a) i) *
        (generatedAxisGlobalSignPlusMinus a).val
          (monsterSpinHadamard (fun t => T t i)) (generatedFifthSpinLow e) := by
  have he : generatedFifthSpinLow e + golayLabelCoefficients (generatedAxisGlobalSignLowCode a) =
      generatedFifthSpinLow (monsterNortonEvenCodeSum a e) +
        (0 : ZMod 2) • (Pi.single 11 1 : SpinIndex) := by
    simpa only [zero_smul, add_zero] using generatedAxisGlobalSignLow_translation a e
  rw [generatedAxisGlobalSign_fourier_low _ _ _ _ _ he,
    generatedAxisGlobalSignLow_ZPhase, generatedAxisGlobalSignPlusMinus_low]
  ring

private theorem actual_fourier_high (a e : Fin 2048)
    (T : SpinIndex → Fin 24 → ℝ) (i : Fin 24) :
    monsterSpinHadamard (fun t =>
      localTensorRepresentation
        (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0) T t i)
        (generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex)) =
      qSign (golayEncoder (monsterNortonYCode a) i) *
        (generatedAxisGlobalSignPlusMinus a).val
          (monsterSpinHadamard (fun t => T t i))
            (generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex)) := by
  have he : generatedFifthSpinLow e + golayLabelCoefficients (generatedAxisGlobalSignLowCode a) =
      generatedFifthSpinLow (monsterNortonEvenCodeSum a e) +
        (0 : ZMod 2) • (Pi.single 11 1 : SpinIndex) := by
    simpa only [zero_smul, add_zero] using generatedAxisGlobalSignLow_translation a e
  rw [generatedAxisGlobalSign_fourier_high _ _ _ _ _ he,
    generatedAxisGlobalSignLow_YPhase, generatedAxisGlobalSignPlusMinus_high]
  calc
    _ = ((if (golayEncodedMask e.val).testBit i.val then (-1 : ℝ) else 1) *
        (if (golayEncodedMask (monsterNortonEvenCodeSum a e).val).testBit i.val then -1 else 1)) *
      qSign (spinDot (sourceCodeThetaPolynomial (generatedFifthSpinLow e)) (monsterNortonYCode a)) *
        monsterSpinHadamard (fun t => T t i)
          (generatedFifthSpinLow (monsterNortonEvenCodeSum a e) + (Pi.single 11 1 : SpinIndex)) :=
      by ring
    _ = _ := by rw [generatedAxisGlobalSignLow_code_signs]; ring

/-- Every actual physical tensor output is the prescribed spin column and genuine physical sign. -/
theorem generatedAxisGlobalSignLow_tensor (a : Fin 2048)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0) T t i =
      qSign (golayEncoder (monsterNortonYCode a) i) *
        (generatedAxisGlobalSignSpin a).val (fun u => T u i) t := by
  have h : monsterSpinHadamard (fun t =>
      localTensorRepresentation
        (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0) T t i) =
      monsterSpinHadamard (qSign (golayEncoder (monsterNortonYCode a) i) •
        (generatedAxisGlobalSignSpin a).val (fun u => T u i)) := by
    rw [map_smul, generatedAxisGlobalSignSpin_fourier]
    funext u
    simp only [Pi.smul_apply, smul_eq_mul]
    obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 u
    by_cases hk : k.val < 2048
    · let e : Fin 2048 := ⟨k.val, hk⟩
      have hr : golayLabelCoefficients k = generatedFifthSpinLow e := by
        change golayLabelCoefficients k = golayLabelCoefficients ⟨e.val, by omega⟩
        congr 1
      rw [hr]
      exact actual_fourier_low a e T i
    · let e : Fin 2048 := ⟨k.val - 2048, by omega⟩
      have hr : golayLabelCoefficients k =
          generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex) := by
        change golayLabelCoefficients k =
          golayLabelCoefficients ⟨e.val, by omega⟩ + Pi.single 11 1
        rw [golayLabel_low_add_omega]
        apply congrArg golayLabelCoefficients
        apply Fin.ext
        dsimp [e]
        omega
      rw [hr]
      exact actual_fourier_high a e T i
  have he := monsterSpinHadamard_involutive.injective h
  exact congrFun he t

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
