/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite source dictionary and support bridges for the first literal Norton line word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The reached integer label gives precisely the displayed source code. -/
theorem monsterNortonLine01ShortInputCode_actual (a : Fin 64) :
    spinDictionaryCode (golayLabelCoefficients (monsterNortonLine01InitialSpinIndices a)) =
      monsterNortonLine01ShortInputCode a := by
  simp only [spinDictionaryCode, spinDictionaryLabel_coeff, monsterNortonLine01ShortInputCode]

/-- A finite polar formula for the actual source X phase avoids the implicit short dictionary. -/
def monsterNortonSourceXQFinitePhase (q : Q) (d : Fin 2048) (j : Fin 24) : ZMod 2 :=
  qBeta (toAdd q.base)
      (toAdd (monsterNortonShortQSource (Sum.inr (Sum.inr (d, j)))).base) +
    qBeta (toAdd (monsterNortonShortQSource (Sum.inr (Sum.inr (d, j)))).base) (toAdd q.base)

/-- The finite preferred-Q formula equals the true source phase with its complete central sign. -/
theorem monsterNortonSourceXQFinitePhase_actual (q : Q) (d : Fin 2048) (j : Fin 24) :
    monsterNortonSourceXQPhase q d j = monsterNortonSourceXQFinitePhase q d j := by
  rw [monsterNortonSourceXQPhase, ← monsterNortonShortQSource_eq]
  rfl

set_option maxRecDepth 10000 in
/-- Every nonzero physical numerator column is one of the sixteen displayed coordinates. -/
theorem monsterNortonLine01ShortPhysicalColumn_cover (i : Fin 24)
    (hi : monsterNortonUNumerator1 i 0 ≠ 0) :
    ∃ k : Fin 16, monsterNortonLine01ShortPhysicalColumn k = i := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
