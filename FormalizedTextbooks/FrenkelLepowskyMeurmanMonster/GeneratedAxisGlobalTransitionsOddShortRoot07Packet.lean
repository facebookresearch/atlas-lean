/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot07Batch00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot07Batch01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot07Batch02

/-! The complete actual signed-short constituent of original odd-family root 7. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All 552 original preferred coordinates have their exact actual source signs and labels. -/
theorem generatedAxisGlobalOddShortRoot07_packet :
    localShortOperator (generatedAxisGlobalOddSourceRootFiber 7)
        ((griessConwayEncode generatedOddAxis).2.1) =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddShortRootPhases 7
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddShortRootLabels 7
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  apply generatedAxisGlobalOddShortBatches_transport 7
    generatedAxisGlobalOddRootQCache07_certificate
  intro j i
  fin_cases j
  · exact generatedAxisGlobalOddShortRoot07Batch00_QImage i
  · exact generatedAxisGlobalOddShortRoot07Batch01_QImage i
  · exact generatedAxisGlobalOddShortRoot07Batch02_QImage i

/-- The entire genuine Griess root word has the same verified complete short constituent. -/
theorem generatedAxisGlobalOddShortRoot07_actual :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 7) generatedOddAxis)).2.1 =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddShortRootPhases 7
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddShortRootLabels 7
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  rw [generatedAxisGlobalOddSourceRootFiber_encode, localConwayRawRepresentation_apply]
  exact generatedAxisGlobalOddShortRoot07_packet

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
