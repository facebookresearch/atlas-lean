/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonRationalData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00FastTensorStateAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06FastTensorStateAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00ShortPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01ShortPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02ShortPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FastTensorPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01FastTensorPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02FastTensorPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonPairingData

/-! Complete original source vector bindings for rational and sparse transition packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every rational input coordinate belongs to the entire literal original local source word. -/
theorem generatedAxisGlobalOddRationalRootPacket_actual (k : Fin 2) :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddRationalRootIndex k)) generatedOddAxis) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalOddRationalRootPacket k) := by
  apply Prod.ext
  · exact generatedAxisGlobalOddRootMatrix_actual _
  · apply Prod.ext
    · funext r
      exact generatedAxisGlobalOddRootShortQ_actual _ r
    · fin_cases k
      · change (griessConwayEncode
          (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 0) generatedOddAxis)).2.2 = _
        rw [generatedAxisGlobalOddRoot00FastTensorState_actual,
          generatedAxisGlobalTensorFactor_rational]
        rfl
      · change (griessConwayEncode
          (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)).2.2 = _
        rw [generatedAxisGlobalOddRoot06FastTensorState_actual,
          generatedAxisGlobalTensorFactor_rational]
        rfl

/-- Replacing the full source sum by its exact sparse lookup changes no input coordinate. -/
theorem generatedAxisGlobalOddSparseRootPacket_actual (k : Fin 2) :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddRationalRootIndex k)) generatedOddAxis) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalOddSparseRootPacket k) := by
  rw [generatedAxisGlobalOddRationalRootPacket_actual]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext r
      fin_cases k
      · exact congrArg (fun z : ℚ => (z : ℝ)) (generatedAxisGlobalOddSparseShortQ_root00 r)
      · exact congrArg (fun z : ℚ => (z : ℝ)) (generatedAxisGlobalOddSparseShortQ_root06 r)
    · rfl

/-- The complete target short packets are the genuine original preferred basis images. -/
theorem generatedAxisGlobalOddRationalComparisonShort_actual (k : Fin 3) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddComparisonLocal k) generatedOddAxis)).2.1 =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddSparseCoefficient ⟨k.val + 2, by omega⟩ p : ℝ) •
          Pi.single (generatedAxisGlobalOddSparseLabel ⟨k.val + 2, by omega⟩ p) (1 : ℝ) := by
  have h (k : Fin 3) :
      (griessConwayEncode
        (rhoLocal (generatedAxisGlobalOddComparisonLocal k) generatedOddAxis)).2.1 =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddComparisonShortPhases k
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddComparisonShortLabels k
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
    fin_cases k
    · exact generatedAxisGlobalOddComparison00Short_actual
    · exact generatedAxisGlobalOddComparison01Short_actual
    · exact generatedAxisGlobalOddComparison02Short_actual
  rw [h]
  fin_cases k
  all_goals simp only [generatedAxisGlobalOddSparseCoefficient,
    generatedAxisGlobalOddSparsePhase, generatedAxisGlobalOddSparseLabel,
    Rat.cast_mul, Rat.cast_intCast, generatedAxisGlobalIntSign_real,
    generatedAxisGlobalOddShortCoefficientQ_actual]
  all_goals rfl

/-- The complete target tensor packets retain their genuine original source denominators. -/
theorem generatedAxisGlobalOddRationalComparisonTensor_actual (k : Fin 3) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddComparisonLocal k) generatedOddAxis)).2.2 =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor (generatedAxisGlobalOddRationalComparisonSpin k)
          (generatedAxisGlobalOddRationalComparisonSpatial k))
        (generatedAxisGlobalOddRationalComparisonDenominator k) := by
  fin_cases k
  · exact generatedAxisGlobalOddComparison00FastTensor_actual
  · exact generatedAxisGlobalOddComparison01FastTensor_actual
  · exact generatedAxisGlobalOddComparison02FastTensor_actual

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
