/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorPairing

/-! Four physical coefficients give every actual source sign tensor output coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original Y and Z pairings are the exact difference and sum of their two physical rows. -/
theorem generatedAxisGlobalTensor_dictionary_pairings (d : Fin 2048) (i : Fin 24)
    (T : SpinIndex → Fin 24 → ℝ) :
    tensorColumnPairing (trialityYTensor d i) T =
      (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
        Real.sqrt 2 / 2 * (T (generatedFifthSpinLow d) i -
          T (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) i) ∧
    tensorColumnPairing (trialityZTensor d i) T =
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        Real.sqrt 2 / 2 * (T (generatedFifthSpinLow d) i +
          T (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) i) := by
  let c : ℝ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
  have hc : c * c = 1 := by dsimp [c]; split_ifs <;> norm_num
  let p : ℝ := qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  have hp : p * p = 1 := qSign_sq _
  have h0 := generatedAxisGlobalTensor_dictionary_pairing d 0 i T
  have h1 := generatedAxisGlobalTensor_dictionary_pairing d 1 i T
  simp only [qSign_zero, zero_smul, add_zero, one_mul] at h0
  simp only [qSign_one, one_smul, neg_one_mul] at h1
  change Real.sqrt 2 * T (generatedFifthSpinLow d) i =
    c * tensorColumnPairing (trialityYTensor d i) T +
      p * tensorColumnPairing (trialityZTensor d i) T at h0
  change Real.sqrt 2 * T (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) i =
    -c * tensorColumnPairing (trialityYTensor d i) T +
      p * tensorColumnPairing (trialityZTensor d i) T at h1
  constructor
  · have h : c * tensorColumnPairing (trialityYTensor d i) T =
        Real.sqrt 2 / 2 * (T (generatedFifthSpinLow d) i -
          T (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) i) := by
      linarith [h0, h1]
    change tensorColumnPairing (trialityYTensor d i) T = _
    calc
      _ = c * (c * tensorColumnPairing (trialityYTensor d i) T) := by
        rw [← mul_assoc, hc, one_mul]
      _ = _ := by rw [h]; ring
  · have h : p * tensorColumnPairing (trialityZTensor d i) T =
        Real.sqrt 2 / 2 * (T (generatedFifthSpinLow d) i +
          T (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) i) := by
      linarith [h0, h1]
    calc
      _ = p * (p * tensorColumnPairing (trialityZTensor d i) T) := by
        rw [← mul_assoc, hp, one_mul]
      _ = _ := by rw [h]; ring

/-- Each real output coefficient of an original Golay sign word has an exact finite formula. -/
theorem generatedAxisGlobalSign_tensor_coordinate (a : Fin 4096) (ε : ZMod 2)
    (d e : Fin 2048) (b h : ZMod 2)
    (he : generatedFifthSpinLow e + golayLabelCoefficients a =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex))
    (T : SpinIndex → Fin 24 → ℝ) (i : Fin 24) :
    2 * localTensorRepresentation (generatedFifthSignFiber a ε) T
        (generatedFifthSpinLow e + b • (Pi.single 11 1 : SpinIndex)) i =
      (qSign b * (if (golayEncodedMask e.val).testBit i.val then (-1 : ℝ) else 1) *
        qSign (generatedAxisGlobalSignYPhase a ε d e) *
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1)) *
          (T (generatedFifthSpinLow d) i -
            T (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) i) +
      qSign (generatedAxisGlobalSignZPhase a e i) *
        (T (generatedFifthSpinLow e) i +
          T (generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex)) i) := by
  have hY := generatedAxisGlobalTensor_pairing_signed (generatedFifthSignFiber a ε) T
    (trialityYTensor d i) (trialityYTensor e i)
    (generatedAxisGlobalSignYPhase a ε d e)
    (generatedAxisGlobalSign_tensor_Y_polynomial a ε d e h he i)
  have hZ := generatedAxisGlobalTensor_pairing_signed (generatedFifthSignFiber a ε) T
    (trialityZTensor e i) (trialityZTensor e i)
    (generatedAxisGlobalSignZPhase a e i)
    (generatedAxisGlobalSign_tensor_Z_polynomial a ε e i)
  have hh := generatedAxisGlobalTensor_dictionary_pairing e b i
    (localTensorRepresentation (generatedFifthSignFiber a ε) T)
  rw [hY, hZ, (generatedAxisGlobalTensor_dictionary_pairings d i T).1,
    (generatedAxisGlobalTensor_dictionary_pairings e i T).2] at hh
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc
    _ = Real.sqrt 2 * (Real.sqrt 2 * localTensorRepresentation
        (generatedFifthSignFiber a ε) T
          (generatedFifthSpinLow e + b • (Pi.single 11 1 : SpinIndex)) i) := by
      rw [← mul_assoc, ← pow_two, hs]
    _ = _ := by
      rw [hh]
      calc
        _ = (qSign b *
            (if (golayEncodedMask e.val).testBit i.val then (-1 : ℝ) else 1) *
            qSign (generatedAxisGlobalSignYPhase a ε d e) *
            (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1)) *
              (T (generatedFifthSpinLow d) i -
                T (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) i) *
                  ((Real.sqrt 2) ^ 2 / 2) +
          qSign (generatedAxisGlobalSignZPhase a e i) *
            (T (generatedFifthSpinLow e) i +
              T (generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex)) i) *
            (qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) *
              qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ)) *
                ((Real.sqrt 2) ^ 2 / 2) := by ring
        _ = _ := by rw [hs, qSign_sq]; ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
