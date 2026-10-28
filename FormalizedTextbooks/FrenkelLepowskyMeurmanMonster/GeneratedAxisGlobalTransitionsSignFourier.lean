/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignTensorCoords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinHadamard

/-! Complete exact low and high Fourier rows of the genuine original source sign action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem low_last (d : Fin 2048) : (generatedFifthSpinLow d) 11 = 0 :=
  golayLabel_low_last d

private theorem high_last (d : Fin 2048) :
    (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) 11 = 1 := by
  simp only [Pi.add_apply, low_last, Pi.single_eq_same, zero_add]

private theorem low_flip (d : Fin 2048) :
    monsterSpinOmegaFlip (generatedFifthSpinLow d) =
      generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex) := rfl

private theorem high_flip (d : Fin 2048) :
    monsterSpinOmegaFlip (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) =
      generatedFifthSpinLow d := by
  change (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) + Pi.single 11 1 = _
  funext j
  change (generatedFifthSpinLow d j + (Pi.single 11 1 : SpinIndex) j) +
    (Pi.single 11 1 : SpinIndex) j = generatedFifthSpinLow d j
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The actual lower Fourier row has the exact source diagonal Z phase. -/
theorem generatedAxisGlobalSign_fourier_low (a : Fin 4096) (ε : ZMod 2)
    (d e : Fin 2048) (h : ZMod 2)
    (he : generatedFifthSpinLow e + golayLabelCoefficients a =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex))
    (T : SpinIndex → Fin 24 → ℝ) (i : Fin 24) :
    monsterSpinHadamard (fun t => localTensorRepresentation (generatedFifthSignFiber a ε) T t i)
      (generatedFifthSpinLow e) =
        qSign (generatedAxisGlobalSignZPhase a e i) *
          monsterSpinHadamard (fun t => T t i) (generatedFifthSpinLow e) := by
  have h0 := generatedAxisGlobalSign_tensor_coordinate a ε d e 0 h he T i
  have h1 := generatedAxisGlobalSign_tensor_coordinate a ε d e 1 h he T i
  simp only [qSign_zero, zero_smul, add_zero, one_mul] at h0
  simp only [qSign_one, one_smul, neg_one_mul] at h1
  have hs : localTensorRepresentation (generatedFifthSignFiber a ε) T
        (generatedFifthSpinLow e) i +
      localTensorRepresentation (generatedFifthSignFiber a ε) T
        (generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex)) i =
      qSign (generatedAxisGlobalSignZPhase a e i) *
        (T (generatedFifthSpinLow e) i +
          T (generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex)) i) := by
    linarith [h0, h1]
  simp only [monsterSpinHadamard_apply, low_last, low_flip, qSign_zero, one_mul]
  change (_ + _) / Real.sqrt 2 = _
  rw [hs]
  ring

/-- The actual upper Fourier row has the exact source relabeling and Y phase. -/
theorem generatedAxisGlobalSign_fourier_high (a : Fin 4096) (ε : ZMod 2)
    (d e : Fin 2048) (h : ZMod 2)
    (he : generatedFifthSpinLow e + golayLabelCoefficients a =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex))
    (T : SpinIndex → Fin 24 → ℝ) (i : Fin 24) :
    monsterSpinHadamard (fun t => localTensorRepresentation (generatedFifthSignFiber a ε) T t i)
      (generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex)) =
        ((if (golayEncodedMask e.val).testBit i.val then (-1 : ℝ) else 1) *
          qSign (generatedAxisGlobalSignYPhase a ε d e) *
          (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1)) *
            monsterSpinHadamard (fun t => T t i)
              (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) := by
  have h0 := generatedAxisGlobalSign_tensor_coordinate a ε d e 0 h he T i
  have h1 := generatedAxisGlobalSign_tensor_coordinate a ε d e 1 h he T i
  simp only [qSign_zero, zero_smul, add_zero, one_mul] at h0
  simp only [qSign_one, one_smul, neg_one_mul] at h1
  have hs : -localTensorRepresentation (generatedFifthSignFiber a ε) T
        (generatedFifthSpinLow e + (Pi.single 11 1 : SpinIndex)) i +
      localTensorRepresentation (generatedFifthSignFiber a ε) T
        (generatedFifthSpinLow e) i =
      ((if (golayEncodedMask e.val).testBit i.val then (-1 : ℝ) else 1) *
        qSign (generatedAxisGlobalSignYPhase a ε d e) *
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1)) *
          (-T (generatedFifthSpinLow d + (Pi.single 11 1 : SpinIndex)) i +
            T (generatedFifthSpinLow d) i) := by
    linarith [h0, h1]
  simp only [monsterSpinHadamard_apply, high_last, high_flip, qSign_one, neg_one_mul]
  rw [hs]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
