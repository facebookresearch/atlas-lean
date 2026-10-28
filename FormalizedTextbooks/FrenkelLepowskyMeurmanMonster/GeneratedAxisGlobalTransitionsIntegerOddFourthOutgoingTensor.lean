/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerOddSourceShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerTensorOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthPhysicalOutgoingTensor

/-! Both original signed outgoing tensors retain their full source coordinates and denominator sixteen. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- All original root-two and root-four source tensor coordinates over their common denominator eight. -/
def generatedAxisGlobalIntegerOddFourthSourceTensor (k : Fin 4)
    (a : Fin 4096) (i : Fin 24) : ℤ :=
  if k.val < 2 then generatedAxisGlobalOddRoot02Spin11 a * generatedAxisGlobalOddRoot02Spatial11 i
    else 2 * generatedAxisGlobalOddRoot04Spin09 a * generatedAxisGlobalOddRoot04Spatial09 i

/-- The integer source factors restore every actual original rational source tensor coordinate. -/
theorem generatedAxisGlobalIntegerOddFourthSourceTensor_rat (k : Fin 4) :
    generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerOddFourthSourceTensor k) 8 =
      generatedAxisGlobalOddFourthPhysicalSourceTensor k := by
  funext a i
  by_cases hk : k.val < 2
  all_goals
    simp only [generatedAxisGlobalIntegerTensorRat, generatedAxisGlobalIntegerOddFourthSourceTensor,
      generatedAxisGlobalOddFourthPhysicalSourceTensor, hk, ↓reduceIte, Int.cast_mul, Int.cast_ofNat] <;> ring

/-- Every source short coefficient, full sign, and both original tensor inputs of the actual signed output. -/
def generatedAxisGlobalIntegerOddFourthOutgoingTensor (k : Fin 4)
    (a : Fin 4096) (i : Fin 24) : ℤ :=
  let d := generatedAxisGlobalSpinLabelLow a
  let s := generatedAxisGlobalIntSign (golayLabelCoefficients a 11)
  let e := generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  let z : ℤ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
  let C := generatedAxisGlobalIntegerOddSourceShort (if k.val < 2 then 0 else 2)
    (Sum.inr (Sum.inr (d,i)))
  let lo := generatedAxisGlobalIntegerOddFourthSourceTensor k ⟨d.val, by omega⟩ i
  let hi := generatedAxisGlobalIntegerOddFourthSourceTensor k ⟨d.val+2048, by omega⟩ i
  if k = 0 ∨ k = 2 then 4*s*z*C + e*z*(lo-hi)
    else 4*e*C+s*e*z*(lo+hi)

/-- Denominator sixteen restores every coordinate of the complete original actual outgoing tensor. -/
theorem generatedAxisGlobalIntegerOddFourthOutgoingTensor_rat (k : Fin 4) :
    generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerOddFourthOutgoingTensor k) 16 =
      generatedAxisGlobalOddFourthPhysicalOutgoingTensor k := by
  funext a i
  dsimp only [generatedAxisGlobalIntegerTensorRat, generatedAxisGlobalIntegerOddFourthOutgoingTensor,
    generatedAxisGlobalOddFourthPhysicalOutgoingTensor]
  rw [← generatedAxisGlobalIntegerOddSourceShort_rat]
  have hlo := congrFun (congrFun (generatedAxisGlobalIntegerOddFourthSourceTensor_rat k)
    ⟨(generatedAxisGlobalSpinLabelLow a).val, by omega⟩) i
  have hhi := congrFun (congrFun (generatedAxisGlobalIntegerOddFourthSourceTensor_rat k)
    ⟨(generatedAxisGlobalSpinLabelLow a).val+2048, by omega⟩) i
  rw [← hlo, ← hhi]
  dsimp only [generatedAxisGlobalIntegerTensorRat]
  by_cases hs : k = 0 ∨ k = 2
  all_goals
    cases hb : (golayEncodedMask (generatedAxisGlobalSpinLabelLow a).val).testBit i.val
    all_goals
      simp only [hs, Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_sub, Int.cast_mul,
        Int.cast_neg, Int.cast_one, Int.cast_ofNat]
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
