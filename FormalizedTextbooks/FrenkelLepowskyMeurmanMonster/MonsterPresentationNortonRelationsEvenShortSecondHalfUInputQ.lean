/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full preferred-Q binary input dictionaries for the actual sparse forward-U half calculation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUInputParity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The coefficient-zero lift encoded by each stored actual hyperbolic mask. -/
def monsterNortonSecondHalfUInputQ (i : NortonSecondHalfShortIndex) : Q :=
  ⟨ofAdd (fun j : Fin 24 =>
    if (monsterNortonSecondHalfShortMask (monsterNortonSecondHalfShortStorage i)).testBit j.val
      then 1 else 0), 1⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Check every hyperbolic coordinate after replacing the actual lattice parity by its proved mask.
/-- Every stored mask is the complete original preferred Q input,
with its genuine zero coefficient. -/
theorem monsterNortonSecondHalfUInputQ_actual (i : NortonSecondHalfShortIndex) :
    monsterNortonShortQ (monsterNortonSecondHalfShortInput i) =
      monsterNortonSecondHalfUInputQ i := by
  unfold monsterNortonShortQ monsterNortonSecondHalfUInputQ
  rw [monsterNortonSecondHalfInputIntegral_actual]
  have hpar : integerParity (monsterNortonLeechCoordinates
      (monsterNortonSecondHalfInputIntegral i)) =
        (fun j : Fin 24 =>
          if (monsterNortonSecondHalfShortParity (monsterNortonSecondHalfShortStorage i)).testBit
            j.val then 1 else 0) := funext (monsterNortonSecondHalfUInputParity_actual i)
  rw [hpar]
  clear hpar
  apply NormalizedCocycleExtension.Extension.ext
  · funext j
    revert i j
    decide +kernel
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
