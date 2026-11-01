/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStagePacket01_00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStagePacket01_01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStagePacket01_02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStagePacket01_03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStagePacket01_04

/-! All original source stages retain their whole binary and central coordinate images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The complete original thirty-stage certificate has no omitted coordinates or central phases. -/
theorem generatedAxisGlobalOddFifthQStageCheck01 (n : Fin 30) (i : Fin 24) :
    generatedAxisGlobalOddFifthQStageCoordinate 1 n i =
      generatedAxisGlobalOddFifthQStageCache 1 ⟨n.val+1, by omega⟩ i := by
  fin_cases n
  · exact generatedAxisGlobalOddFifthQStagePacket01_00 0 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_00 1 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_00 2 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_00 3 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_00 4 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_00 5 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_01 0 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_01 1 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_01 2 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_01 3 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_01 4 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_01 5 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_02 0 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_02 1 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_02 2 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_02 3 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_02 4 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_02 5 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_03 0 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_03 1 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_03 2 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_03 3 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_03 4 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_03 5 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_04 0 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_04 1 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_04 2 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_04 3 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_04 4 i
  · exact generatedAxisGlobalOddFifthQStagePacket01_04 5 i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
