/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A finite thirteen-cycle certificate for the actual central-corrected Norton Q action. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImage
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The thirteen positive normal coefficients encountered in the actual Norton orbit. -/
def monsterNortonNormalQData (i : Fin 13) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients (![0,1024,0,3087,0,0,0,0,0,3073,0,0,0] i))
    (golayLabelCoefficients (![0,0,2733,0,2775,2487,2539,2919,2397,0,2683,2971,3069] i))),
    1⟩

/-- Multiply by the actual v lift to obtain the genuine Q orbit state. -/
def monsterNortonOrbitQData (i : Fin 13) : Q := monsterNortonNormalQData i * y555NortonVQ

set_option maxHeartbeats 8000000 in
-- Each branch checks all 24 binary coordinates and the central phase of the seven-factor word.
set_option maxRecDepth 10000 in
/-- The displayed data is a thirteen-cycle of the actual complete Norton u conjugation. -/
theorem monsterNortonOrbitQData_step (i : Fin 13) :
    monsterNortonUQImage (monsterNortonOrbitQData i) =
      monsterNortonOrbitQData ⟨(i.val + 1) % 13, Nat.mod_lt _ (by omega)⟩ := by
  fin_cases i <;> apply NormalizedCocycleExtension.Extension.ext
  all_goals apply Multiplicative.toAdd.injective
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
