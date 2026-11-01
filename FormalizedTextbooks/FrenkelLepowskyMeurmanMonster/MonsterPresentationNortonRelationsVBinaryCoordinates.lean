/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Propositional binary coordinates for the actual source Norton involution. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQShortDiagonal

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The finite translation/modulation mask of the literal Norton V word. -/
def monsterNortonVBinaryCoordinates : Fin 24 → ZMod 2 :=
  fun i => if (0x80140e : ℕ).testBit i.val then 1 else 0

/-- The cached mask is the actual Q binary vector, propositionally rather than by unfolding. -/
theorem monsterNortonVBinaryCoordinates_actual :
    toAdd y555NortonVQ.base = monsterNortonVBinaryCoordinates := by
  funext i
  apply ZMod.val_injective 2
  rw [monsterNortonVQ_coordinate_certificate.1 i]
  unfold monsterNortonVBinaryCoordinates
  split_ifs <;> rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
