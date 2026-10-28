/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerOddSourceShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerTensorOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthOutgoingPacket

/-! Both original signed outgoing tensors retain their full source coordinates and denominator sixteen. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every original root-three source tensor coordinate over its exact denominator eight. -/
def generatedAxisGlobalIntegerOddFifthSourceTensor
    (a : Fin 4096) (i : Fin 24) : ℤ :=
  generatedAxisGlobalOddRoot03Spin09 a * generatedAxisGlobalOddRoot03Spatial09 i

/-- Every source short coefficient, full sign, and both original tensor inputs of the actual signed output. -/
def generatedAxisGlobalIntegerOddFifthOutgoingTensor (k : Fin 2)
    (a : Fin 4096) (i : Fin 24) : ℤ :=
  let d := generatedAxisGlobalSpinLabelLow a
  let s := generatedAxisGlobalIntSign (golayLabelCoefficients a 11)
  let e := generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  let z : ℤ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
  let C := generatedAxisGlobalIntegerOddSourceShort 1
    (Sum.inr (Sum.inr (d,i)))
  let lo := generatedAxisGlobalIntegerOddFifthSourceTensor ⟨d.val, by omega⟩ i
  let hi := generatedAxisGlobalIntegerOddFifthSourceTensor ⟨d.val+2048, by omega⟩ i
  if k = 0 then 4*s*z*C + e*z*(lo-hi)
    else 4*e*C+s*e*z*(lo+hi)

/-- Denominator sixteen restores every coefficient of the original root-three outgoing tensor. -/
theorem generatedAxisGlobalIntegerOddFifthOutgoingTensor_rat (k : Fin 2) :
    generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerOddFifthOutgoingTensor k) 16 =
      generatedAxisGlobalOddFifthOutgoingTensor k := by
  funext a i
  fin_cases k
  · change (generatedAxisGlobalIntegerOddFifthOutgoingTensor 0 a i : ℚ) / 16 =
      generatedAxisGlobalTrialityScaledTensorQ generatedAxisGlobalOddRoot03RationalPacket.2.1
        generatedAxisGlobalOddRoot03RationalPacket.2.2
        (golayLabelCoefficients a) i
    dsimp only [generatedAxisGlobalIntegerOddFifthOutgoingTensor,
      generatedAxisGlobalIntegerOddFifthSourceTensor, generatedAxisGlobalTrialityScaledTensorQ,
      generatedAxisGlobalOddRoot03RationalPacket]
    simp only [generatedAxisGlobalSpinLabel_coeff]
    norm_num only
    rw [← generatedAxisGlobalIntegerOddSourceShort_rat]
    cases hb : (golayEncodedMask (generatedAxisGlobalSpinLabelLow a).val).testBit i.val
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_sub, Int.cast_mul,
        Int.cast_neg, Int.cast_one, Int.cast_ofNat]
      ring
  · change (generatedAxisGlobalIntegerOddFifthOutgoingTensor 1 a i : ℚ) / 16 =
      generatedAxisGlobalInverseTensorQ generatedAxisGlobalOddRoot03RationalPacket
        (golayLabelCoefficients a) i
    dsimp only [generatedAxisGlobalIntegerOddFifthOutgoingTensor,
      generatedAxisGlobalIntegerOddFifthSourceTensor, generatedAxisGlobalInverseTensorQ,
      generatedAxisGlobalOddRoot03RationalPacket]
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    simp only [generatedAxisGlobalSpinLabel_coeff]
    norm_num only
    rw [← generatedAxisGlobalIntegerOddSourceShort_rat]
    cases hb : (golayEncodedMask (generatedAxisGlobalSpinLabelLow a).val).testBit i.val
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_sub, Int.cast_mul,
        Int.cast_neg, Int.cast_one, Int.cast_ofNat]
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
