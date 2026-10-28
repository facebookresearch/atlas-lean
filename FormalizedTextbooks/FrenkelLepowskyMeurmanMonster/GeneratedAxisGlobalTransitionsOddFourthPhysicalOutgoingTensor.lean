/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthOutgoingPacket

/-! Whole actual signed outgoing tensors evaluated in their original physical labels. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The complete original source tensor factors at every physical label. -/
def generatedAxisGlobalOddFourthPhysicalSourceTensor (k : Fin 4)
    (a : Fin 4096) (i : Fin 24) : ℚ :=
  if k.val < 2 then
    (generatedAxisGlobalOddRoot02Spin11 a : ℚ) * (generatedAxisGlobalOddRoot02Spatial11 i : ℚ) / 8
  else (generatedAxisGlobalOddRoot04Spin09 a : ℚ) * (generatedAxisGlobalOddRoot04Spatial09 i : ℚ) / 4

/-- Every original odd-short input, central sign, and both original tensor inputs is retained. -/
def generatedAxisGlobalOddFourthPhysicalOutgoingTensor (k : Fin 4)
    (a : Fin 4096) (i : Fin 24) : ℚ :=
  let d := generatedAxisGlobalSpinLabelLow a
  let s : ℚ := generatedAxisGlobalIntSign (golayLabelCoefficients a 11)
  let e : ℚ := generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  let z : ℚ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
  let C := generatedAxisGlobalOddOtherSparseShortQ (if k.val < 2 then 0 else 2)
    (Sum.inr (Sum.inr (d,i)))
  let lo := generatedAxisGlobalOddFourthPhysicalSourceTensor k ⟨d.val, by omega⟩ i
  let hi := generatedAxisGlobalOddFourthPhysicalSourceTensor k ⟨d.val+2048, by omega⟩ i
  if k = 0 ∨ k = 2 then s*z*C + e*z*(lo-hi)/2
  else e*C+s*e*z*(lo+hi)/2

/-- The entire physical tensor equals every original actual outgoing tensor coefficient. -/
theorem generatedAxisGlobalOddFourthPhysicalOutgoingTensor_eq (k : Fin 4) :
    generatedAxisGlobalOddFourthPhysicalOutgoingTensor k = generatedAxisGlobalOddFourthOutgoingTensor k := by
  funext a i
  fin_cases k <;>
    simp [generatedAxisGlobalOddFourthPhysicalOutgoingTensor,
      generatedAxisGlobalOddFourthPhysicalSourceTensor,
      generatedAxisGlobalOddFourthOutgoingTensor,
      generatedAxisGlobalOddFourthOutgoingPacket,
      generatedAxisGlobalRationalTriality, generatedAxisGlobalRationalInverse,
      generatedAxisGlobalTrialityScaledTensorQ, generatedAxisGlobalInverseTensorQ,
      generatedAxisGlobalOddRoot02RationalPacket, generatedAxisGlobalOddRoot04RationalPacket,
      generatedAxisGlobalSpinLabel_coeff]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
