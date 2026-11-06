/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortSource

/-! Actual preferred-Q coordinates of the pair family, with explicit increasing coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The source pair lift evaluated with its actual Golay syndrome character. -/
def generatedFourthLiftShortPairQ (s : Fin 2) (a b : Fin 24) : Q :=
  ⟨ofAdd (Fin.append (if s = 0 then 0 else Pi.single 11 1)
    (fun k => (golayGeneratorBit k a : ZMod 2) + (golayGeneratorBit k b : ZMod 2))), 1⟩

/-- Explicit pair coordinates evaluate the genuine preferred short lift. -/
theorem generatedFourth_lift_short_pair_q (s : Fin 2) (a b : Fin 24) (hab : a < b) :
    generatedFourthLiftShortPairQ s a b =
      griessShortQ (Sum.inl (s, griessPairIndex a b (ne_of_lt hab))) := by
  rw [← monsterNortonShortQSource_actual]
  simp only [monsterNortonShortQSource, monsterNortonShortTranslation,
    monsterNortonShortModulation, generatedFourthLiftShortPairQ]
  have hs : griessPairSyndrome (griessPairIndex a b (ne_of_lt hab)) =
      (fun k => (golayGeneratorBit k a : ZMod 2) + (golayGeneratorBit k b : ZMod 2)) := by
    funext k
    simp only [griessPairSyndrome, griessPairIndex_coordinates, hab, ite_true]
  rw [hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
