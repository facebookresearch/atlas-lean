/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStagePacket00_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStagePacket00_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStagePacket00_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStagePacket00_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStagePacket00_04

/-! All original source stages retain their whole binary and central coordinate images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The complete original thirty-stage certificate has no omitted coordinates or central phases. -/
theorem generatedAxisGlobalOddFifthQStageCheck00 (n : Fin 30) (i : Fin 24) :
    generatedAxisGlobalOddFifthQStageCoordinate 0 n i =
      generatedAxisGlobalOddFifthQStageCache 0 ⟨n.val+1, by omega⟩ i := by
  fin_cases n
  · exact generatedAxisGlobalOddFifthQStagePacket00_00 0 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_00 1 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_00 2 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_00 3 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_00 4 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_00 5 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_01 0 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_01 1 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_01 2 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_01 3 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_01 4 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_01 5 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_02 0 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_02 1 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_02 2 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_02 3 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_02 4 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_02 5 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_03 0 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_03 1 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_03 2 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_03 3 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_03 4 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_03 5 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_04 0 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_04 1 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_04 2 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_04 3 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_04 4 i
  · exact generatedAxisGlobalOddFifthQStagePacket00_04 5 i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
