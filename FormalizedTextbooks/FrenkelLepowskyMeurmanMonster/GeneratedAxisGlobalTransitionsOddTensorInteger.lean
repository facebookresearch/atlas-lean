/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddCoordinates

/-! The complete original odd-axis tensor has an exact integer numerator packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original two-point Hadamard tensor numerator, retaining every physical zero coordinate. -/
def generatedAxisGlobalOddTensorInteger (k : Fin 4096) (i : Fin 24) : ℤ :=
  -8 * generatedAxisGlobalIntSign ((golayLabelCoefficients k) 11) *
    (if spinDictionaryCode (golayLabelCoefficients k) = 0 then 1 else 0) *
    (if i = 0 then 1 else 0)

/-- The whole actual odd-axis tensor is precisely the original denominator-one integer packet. -/
theorem generatedAxisGlobalOddTensorInteger_packet :
    (griessConwayEncode generatedOddAxis).2.2 =
      generatedAxisGlobalTensorIntegerPacket generatedAxisGlobalOddTensorInteger 1 := by
  rw [generatedOddAxis, generatedAxis_triality_odd_tensor]
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
  rw [generatedAxisGlobalTensorIntegerPacket_coefficient]
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  simp only [Pi.smul_apply, smul_eq_mul, qSign_zero, mul_one, trialityYTensor, Fin.val_zero,
    hm, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte,
    generatedAxisGlobalOddTensorInteger, Int.cast_mul, Int.cast_neg, Int.cast_ofNat,
    Int.cast_ite, Int.cast_one, Int.cast_zero, Nat.cast_one, one_mul,
    generatedAxisGlobalIntSign_real]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
