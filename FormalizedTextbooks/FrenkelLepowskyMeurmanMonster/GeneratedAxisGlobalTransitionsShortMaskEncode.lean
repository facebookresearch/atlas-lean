/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMaskCheck
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortQFinite
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthPacketQFinite

/-! The actual preferred short lifts are positive sections in the original Q extension. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual finite preferred-short lift has its exact original coefficient-zero section. -/
theorem generatedAxisGlobalShortQFinite_positive (r : GriessShortIndex) :
    (generatedAxisGlobalShortQFinite r).coeff = 1 := by
  rw [generatedAxisGlobalShortQFinite_actual, ← monsterNortonShortQSource_actual]
  rfl

/-- Every actual fifth-packet input has its exact original coefficient-zero section. -/
theorem generatedAxisGlobalFifthPacketQFinite_positive
    (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    (generatedAxisGlobalFifthPacketQFinite i).coeff = 1 := by
  rw [generatedAxisGlobalFifthPacketQFinite_actual, ← monsterNortonShortQSource_actual]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
