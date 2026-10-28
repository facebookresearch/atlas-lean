/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A physical minus-pair representative for the actual short-class trace calculation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryLeechPolar
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTraceCentral

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original short-coordinate label of the physical vector four times e₀ minus e₁. -/
def monsterGeometryShortBaseIndex : GriessShortIndex :=
  Sum.inl (0, griessPairIndex 0 1 (by decide))

/-- Its preferred actual extraspecial lift. -/
def monsterGeometryShortBaseQ : Q := griessShortQ monsterGeometryShortBaseIndex

/-- The chosen source representative is literally the physical minus pair. -/
theorem monsterGeometryShortBase_vector :
    griessShortIntegral monsterGeometryShortBaseIndex =
      (4 : ℤ) • Pi.single (0 : Fin 24) 1 - (4 : ℤ) • Pi.single (1 : Fin 24) 1 := by
  funext i
  simp only [monsterGeometryShortBaseIndex, griessShortIntegral, griessPairIndex_coordinates]
  norm_num [Pi.single_apply]
  split_ifs <;> ring

/-- Its physical inner product reads just the first two original integer coordinates. -/
theorem monsterGeometryShortBase_dot (r : GriessShortIndex) :
    dotProduct (griessShortIntegral monsterGeometryShortBaseIndex) (griessShortIntegral r) =
      4 * (griessShortIntegral r 0 - griessShortIntegral r 1) := by
  rw [monsterGeometryShortBase_vector, sub_dotProduct, smul_dotProduct, smul_dotProduct]
  simp [mul_sub]

/-- The chosen lift's short phase is the parity of the coordinate difference divided by two. -/
theorem monsterGeometryShortBase_phase (r : GriessShortIndex) :
    qBeta (toAdd monsterGeometryShortBaseQ.base) (toAdd (griessShortQ r).base) +
        qBeta (toAdd (griessShortQ r).base) (toAdd monsterGeometryShortBaseQ.base) =
      (((griessShortIntegral r 0 - griessShortIntegral r 1) / 2 : ℤ) : ZMod 2) := by
  change co1BinaryPolar
    (leechHyperbolicCoordinates (griessShortClass monsterGeometryShortBaseIndex))
    (leechHyperbolicCoordinates (griessShortClass r)) = _
  rw [griessShortClass, griessShortClass, monsterGeometryLeech_polar]
  change ((dotProduct (griessShortIntegral monsterGeometryShortBaseIndex)
    (griessShortIntegral r) / 8 : ℤ) : ZMod 2) = _
  rw [monsterGeometryShortBase_dot]
  congr 1
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
