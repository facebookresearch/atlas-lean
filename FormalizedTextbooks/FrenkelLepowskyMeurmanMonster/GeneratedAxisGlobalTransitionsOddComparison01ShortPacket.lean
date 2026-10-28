/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonShortAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01ShortBatch00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01ShortBatch01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01ShortBatch02

/-! The complete actual signed-short constituent of original original local comparison 1. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All 552 original preferred coordinates have their exact actual source signs and labels. -/
theorem generatedAxisGlobalOddComparison01Short_packet :
    localShortOperator (generatedAxisGlobalOddComparisonFiber 1)
        ((griessConwayEncode generatedOddAxis).2.1) =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddComparisonShortPhases 1
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddComparisonShortLabels 1
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  apply generatedAxisGlobalOddComparisonShortBatches_transport 1
  intro j i
  fin_cases j
  · exact generatedAxisGlobalOddComparison01ShortBatch00_QImage i
  · exact generatedAxisGlobalOddComparison01ShortBatch01_QImage i
  · exact generatedAxisGlobalOddComparison01ShortBatch02_QImage i

/-- The entire genuine Griess root word has the same verified complete short constituent. -/
theorem generatedAxisGlobalOddComparison01Short_actual :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddComparisonLocal 1) generatedOddAxis)).2.1 =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddComparisonShortPhases 1
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddComparisonShortLabels 1
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  rw [generatedAxisGlobalOddComparisonFiber_encode, localConwayRawRepresentation_apply]
  exact generatedAxisGlobalOddComparison01Short_packet

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
