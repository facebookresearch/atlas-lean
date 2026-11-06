/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite preferred-Q source coordinates of an octad without enumerating all octads. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The finite source-Q lift of a displayed code and its eight physical octad positions. -/
def monsterNortonOctadQSource (a : Fin 4096) (p : Fin 8 → Fin 24) (e : Fin 64) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients a + griessOctadOmegaCoefficient e • Pi.single 11 1)
    (sourceWordTheta a + golaySyndrome (integerParity
      (fun i => if (monsterNortonOctadCoordinateSignMask p e).testBit i.val then 1 else 0)))),
    1⟩

/-- The finite eight-position formula is the complete actual preferred-Q source lift. -/
theorem monsterNortonOctadQSource_actual (a : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8) (p : Fin 8 → Fin 24)
    (hp : ∀ k, golayOctadCoordinate (monsterNortonOctadIndex a ha) k = p k)
    (e : Fin 64) :
    monsterNortonShortQSource (Sum.inr (Sum.inl (monsterNortonOctadIndex a ha, e))) =
      monsterNortonOctadQSource a p e := by
  have hn : griessOctadNegativeInteger (monsterNortonOctadIndex a ha) e =
      (fun i => if (monsterNortonOctadCoordinateSignMask p e).testBit i.val then 1 else 0) := by
    funext i
    rw [griessOctadNegativeInteger, monsterNortonOctadCoordinateSignMask_eq _ p hp]
  simp only [monsterNortonShortQSource, monsterNortonShortTranslation,
    monsterNortonShortModulation, monsterNortonOctadIndex_label, hn,
    monsterNortonOctadQSource]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
