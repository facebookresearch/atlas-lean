/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonShortAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02ShortBatch00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02ShortBatch01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02ShortBatch02

/-! The complete actual signed-short constituent of original original local comparison 2. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All 552 original preferred coordinates have their exact actual source signs and labels. -/
theorem generatedAxisGlobalOddComparison02Short_packet :
    localShortOperator (generatedAxisGlobalOddComparisonFiber 2)
        ((griessConwayEncode generatedOddAxis).2.1) =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddComparisonShortPhases 2
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddComparisonShortLabels 2
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  apply generatedAxisGlobalOddComparisonShortBatches_transport 2
  intro j i
  fin_cases j
  · exact generatedAxisGlobalOddComparison02ShortBatch00_QImage i
  · exact generatedAxisGlobalOddComparison02ShortBatch01_QImage i
  · exact generatedAxisGlobalOddComparison02ShortBatch02_QImage i

/-- The entire genuine Griess root word has the same verified complete short constituent. -/
theorem generatedAxisGlobalOddComparison02Short_actual :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddComparisonLocal 2) generatedOddAxis)).2.1 =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddComparisonShortPhases 2
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddComparisonShortLabels 2
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  rw [generatedAxisGlobalOddComparisonFiber_encode, localConwayRawRepresentation_apply]
  exact generatedAxisGlobalOddComparison02Short_packet

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
