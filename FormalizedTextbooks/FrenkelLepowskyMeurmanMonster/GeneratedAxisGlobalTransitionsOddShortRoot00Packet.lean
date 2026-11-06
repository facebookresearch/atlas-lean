/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot00Batch00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot00Batch01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot00Batch02

/-! The complete actual signed-short constituent of original odd-family root 0. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All 552 original preferred coordinates have their exact actual source signs and labels. -/
theorem generatedAxisGlobalOddShortRoot00_packet :
    localShortOperator (generatedAxisGlobalOddSourceRootFiber 0)
        ((griessConwayEncode generatedOddAxis).2.1) =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddShortRootPhases 0
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddShortRootLabels 0
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  apply generatedAxisGlobalOddShortBatches_transport 0
    generatedAxisGlobalOddRootQCache00_certificate
  intro j i
  fin_cases j
  · exact generatedAxisGlobalOddShortRoot00Batch00_QImage i
  · exact generatedAxisGlobalOddShortRoot00Batch01_QImage i
  · exact generatedAxisGlobalOddShortRoot00Batch02_QImage i

/-- The entire genuine Griess root word has the same verified complete short constituent. -/
theorem generatedAxisGlobalOddShortRoot00_actual :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 0) generatedOddAxis)).2.1 =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddShortRootPhases 0
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddShortRootLabels 0
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  rw [generatedAxisGlobalOddSourceRootFiber_encode, localConwayRawRepresentation_apply]
  exact generatedAxisGlobalOddShortRoot00_packet

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
