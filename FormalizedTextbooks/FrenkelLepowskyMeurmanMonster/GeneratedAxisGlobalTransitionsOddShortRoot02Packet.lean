/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot02Batch00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot02Batch01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot02Batch02

/-! The complete actual signed-short constituent of original odd-family root 2. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- All 552 original preferred coordinates have their exact actual source signs and labels. -/
theorem generatedAxisGlobalOddShortRoot02_packet :
    localShortOperator (generatedAxisGlobalOddSourceRootFiber 2)
        ((griessConwayEncode generatedOddAxis).2.1) =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddShortRootPhases 2
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddShortRootLabels 2
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  apply generatedAxisGlobalOddShortBatches_transport 2
    generatedAxisGlobalOddRootQCache02_certificate
  intro j i
  fin_cases j
  · exact generatedAxisGlobalOddShortRoot02Batch00_QImage i
  · exact generatedAxisGlobalOddShortRoot02Batch01_QImage i
  · exact generatedAxisGlobalOddShortRoot02Batch02_QImage i

/-- The entire genuine Griess root word has the same verified complete short constituent. -/
theorem generatedAxisGlobalOddShortRoot02_actual :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis)).2.1 =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddShortRootPhases 2
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddShortRootLabels 2
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  rw [generatedAxisGlobalOddSourceRootFiber_encode, localConwayRawRepresentation_apply]
  exact generatedAxisGlobalOddShortRoot02_packet

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
