/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact bitwise addition and finite shifts for the actual Norton compact spin formula. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactIntegerBasis

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Addition of actual twelve-bit spin labels as bounded integer xor. -/
def monsterNortonBitXor (a b : Fin 4096) : Fin 4096 :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 12) a.isLt b.isLt⟩

/-- The bitwise label operation is exactly addition in the actual binary spin space. -/
theorem monsterNortonBitXor_coeff (a b : Fin 4096) :
    golayLabelCoefficients (monsterNortonBitXor a b) =
      golayLabelCoefficients a + golayLabelCoefficients b := by
  funext i
  simp only [monsterNortonBitXor, golayLabelCoefficients, Nat.testBit_xor, Pi.add_apply]
  cases ha : a.val.testBit i.val <;> cases hb : b.val.testBit i.val <;> decide

/-- Encoding actual binary spin addition yields precisely the bounded integer xor. -/
theorem monsterNortonBitXor_label (a b : SpinIndex) :
    nortonUIntegerLabel (a + b) =
      monsterNortonBitXor (nortonUIntegerLabel a) (nortonUIntegerLabel b) := by
  apply golayLabelCoefficients_injective
  rw [nortonUIntegerLabel_inverse, monsterNortonBitXor_coeff,
    nortonUIntegerLabel_inverse, nortonUIntegerLabel_inverse]

/-- The six actual Gray translation masks evaluated by bounded integer xor. -/
def monsterNortonBitGrayLabel (a : Fin 64) : Fin 4096 :=
  ⟨((if a.val.testBit 0 then 0x400 else 0) ^^^
    (if a.val.testBit 1 then 0xc0f else 0) ^^^
    (if a.val.testBit 2 then 0xc01 else 0) ^^^
    (if a.val.testBit 3 then 0xc02 else 0) ^^^
    (if a.val.testBit 4 then 0xc04 else 0) ^^^
    (if a.val.testBit 5 then 0xc08 else 0)) % 4096, Nat.mod_lt _ (by norm_num)⟩

set_option maxRecDepth 10000 in
/-- Every bitwise Gray label is the actual published Gaussian shift. -/
theorem monsterNortonBitGrayLabel_actual (a : Fin 64) :
    nortonUIntegerLabel (xiGrayCode (monsterNortonGrayCoefficients a)) =
      monsterNortonBitGrayLabel a := by
  revert a
  decide +kernel

/-- The genuine inverse correction phase evaluated through its actual modulation mask. -/
def monsterNortonUCompactBitInversePhase (n : Fin 4096) : ℤ :=
  if monsterNortonBitParity (n.val &&& 0xd03) then 1 else -1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- All twelve-bit phases are checked against the actual inverse Q element, including its center.
/-- The bitwise inverse correction phase is the full actual Q phase. -/
theorem monsterNortonUCompactBitInversePhase_actual (n : Fin 4096) :
    nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection⁻¹
      (golayLabelCoefficients n)) = monsterNortonUCompactBitInversePhase n := by
  revert n
  decide +kernel

/-- The actual inverse correction translates by the precise label 1024. -/
theorem monsterNortonUCompactBitInverseTranslation_actual :
    nortonUIntegerLabel (spinTranslation monsterNortonUCompactCorrection⁻¹) = 1024 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
