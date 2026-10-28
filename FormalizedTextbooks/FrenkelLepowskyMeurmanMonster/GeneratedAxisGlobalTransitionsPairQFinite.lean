/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortPacketQ

/-! Executable full preferred-Q lifts for the actual pair catalogue. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The actual pair lift evaluated through checked physical-coordinate data. -/
def generatedAxisGlobalPairQFinite (s : Fin 2) (p : Fin 276) : Q :=
  ⟨ofAdd (Fin.append (if s = 0 then 0 else Pi.single 11 1)
    (fun k => (golayGeneratorBit k (generatedAxisGlobalPairCoordinates p).1 : ZMod 2) +
      (golayGeneratorBit k (generatedAxisGlobalPairCoordinates p).2 : ZMod 2))), 1⟩

/-- The finite pair formula is the entire actual preferred lift at the original catalogue index. -/
theorem generatedAxisGlobalPairQFinite_actual (s : Fin 2) (p : Fin 276) :
    generatedAxisGlobalPairQFinite s p = griessShortQ (Sum.inl (s, p)) := by
  rw [← monsterNortonShortQSource_actual]
  simp only [generatedAxisGlobalPairQFinite, monsterNortonShortQSource,
    monsterNortonShortTranslation, monsterNortonShortModulation,
    generatedAxisGlobalPairCoordinates_actual]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
