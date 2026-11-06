/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Proved original-coordinate dictionaries for the remaining octad input/output labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadUData

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadOrdering

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual original octad index of a displayed certified source code. -/
noncomputable def monsterNortonRemainingOctadUOctad (c : Fin 76) : Fin 759 :=
  monsterNortonOctadIndex (monsterNortonRemainingOctadUCodes c)
    (monsterNortonRemainingOctadUCodes_weight c)

/-- The displayed positions agree with the original increasing octad enumeration. -/
theorem monsterNortonRemainingOctadUPositions_actual (c : Fin 76) (i : Fin 8) :
    golayOctadCoordinate (monsterNortonRemainingOctadUOctad c) i =
      monsterNortonRemainingOctadUPositions c i :=
  monsterNortonOctadIndex_coordinate_of_strictMono _ _ _
    (monsterNortonRemainingOctadUPositions_mem c)
    (monsterNortonRemainingOctadUPositions_strictMono c) i

/-- Each remaining original input, retaining its local sign pattern. -/
noncomputable def monsterNortonRemainingOctadUInput (k : Fin 10) (e : Fin 64) :
    GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
    (monsterNortonRemainingOctadUInputChoice k), e))

/-- The genuine preferred output in the octad or odd source family. -/
noncomputable def monsterNortonRemainingOctadUOutput (k : Fin 10) (e : Fin 64) :
    GriessShortIndex :=
  if monsterNortonRemainingOctadUOutputIsOctad k e = true then
    Sum.inr (Sum.inl (monsterNortonRemainingOctadUOctad
      (monsterNortonRemainingOctadUOutputChoice k e),
      monsterNortonRemainingOctadUOutputSign k e))
  else Sum.inr (Sum.inr
    (monsterNortonRemainingOctadUOutputOddCode k e,
      monsterNortonRemainingOctadUOutputOddPosition k e))

/-- The computable complete preferred input Q lift in original source coordinates. -/
def monsterNortonRemainingOctadUInputQ (k : Fin 10) (e : Fin 64) : Q :=
  monsterNortonOctadQSource
    (monsterNortonRemainingOctadUCodes (monsterNortonRemainingOctadUInputChoice k))
    (monsterNortonRemainingOctadUPositions (monsterNortonRemainingOctadUInputChoice k)) e

/-- The computable complete preferred output Q lift in original source coordinates. -/
def monsterNortonRemainingOctadUOutputQ (k : Fin 10) (e : Fin 64) : Q :=
  if monsterNortonRemainingOctadUOutputIsOctad k e = true then
    monsterNortonOctadQSource
      (monsterNortonRemainingOctadUCodes (monsterNortonRemainingOctadUOutputChoice k e))
      (monsterNortonRemainingOctadUPositions (monsterNortonRemainingOctadUOutputChoice k e))
      (monsterNortonRemainingOctadUOutputSign k e)
  else monsterNortonShortQSource (Sum.inr (Sum.inr
    (monsterNortonRemainingOctadUOutputOddCode k e,
      monsterNortonRemainingOctadUOutputOddPosition k e)))

/-- Input coordinate evaluation is exactly the actual preferred source lift. -/
theorem monsterNortonRemainingOctadUInputQ_actual (k : Fin 10) (e : Fin 64) :
    monsterNortonShortQSource (monsterNortonRemainingOctadUInput k e) =
      monsterNortonRemainingOctadUInputQ k e := by
  apply monsterNortonOctadQSource_actual
  exact monsterNortonRemainingOctadUPositions_actual _

/-- Output coordinate evaluation is exactly the actual preferred source lift in either family. -/
theorem monsterNortonRemainingOctadUOutputQ_actual (k : Fin 10) (e : Fin 64) :
    monsterNortonShortQSource (monsterNortonRemainingOctadUOutput k e) =
      monsterNortonRemainingOctadUOutputQ k e := by
  unfold monsterNortonRemainingOctadUOutput monsterNortonRemainingOctadUOutputQ
  by_cases h : monsterNortonRemainingOctadUOutputIsOctad k e = true
  · simp only [h, ite_true]
    apply monsterNortonOctadQSource_actual
    exact monsterNortonRemainingOctadUPositions_actual _
  · simp [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
