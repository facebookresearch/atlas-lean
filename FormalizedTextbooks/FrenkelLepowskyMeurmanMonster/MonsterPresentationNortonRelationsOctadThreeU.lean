/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual U transport for all sixty-four original code-three preferred units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadThreeUSupplement
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolInputQ

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual common-pool or supplemental source entry for each original even sign. -/
def monsterNortonOctadThreeUStorage : Fin 64 → Fin 1552 ⊕ Fin 8 :=
  ![
    Sum.inl 160, Sum.inl 161, Sum.inl 162, Sum.inl 163,
    Sum.inl 164, Sum.inl 165, Sum.inr 0, Sum.inl 166,
    Sum.inl 167, Sum.inr 1, Sum.inl 168, Sum.inl 169,
    Sum.inl 170, Sum.inl 171, Sum.inl 172, Sum.inl 173,
    Sum.inl 174, Sum.inl 175, Sum.inl 176, Sum.inr 2,
    Sum.inl 177, Sum.inl 178, Sum.inl 179, Sum.inl 180,
    Sum.inl 181, Sum.inl 182, Sum.inl 183, Sum.inl 184,
    Sum.inr 3, Sum.inl 185, Sum.inl 186, Sum.inl 187,
    Sum.inr 4, Sum.inl 188, Sum.inl 189, Sum.inl 190,
    Sum.inl 191, Sum.inl 192, Sum.inl 193, Sum.inl 194,
    Sum.inl 195, Sum.inl 196, Sum.inl 197, Sum.inl 198,
    Sum.inl 199, Sum.inl 200, Sum.inl 201, Sum.inr 5,
    Sum.inl 202, Sum.inl 203, Sum.inl 204, Sum.inl 205,
    Sum.inl 206, Sum.inr 6, Sum.inl 207, Sum.inl 208,
    Sum.inl 209, Sum.inl 210, Sum.inr 7, Sum.inl 211,
    Sum.inl 212, Sum.inl 213, Sum.inl 214, Sum.inl 215
  ]

/-- The genuine original code-three preferred input unit. -/
noncomputable def monsterNortonOctadThreeUInput (e : Fin 64) : GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonPairHalfUPoolOctadCode 0)
    (monsterNortonPairHalfUPoolOctad_weight 0), e))

/-- The actual preferred output, using only previously checked full U images. -/
noncomputable def monsterNortonOctadThreeUOutput (e : Fin 64) : GriessShortIndex :=
  Sum.elim monsterNortonPairHalfUPoolOutput monsterNortonOctadThreeSupplementOutput
    (monsterNortonOctadThreeUStorage e)

/-- Every selected dictionary entry is the whole actual original input unit. -/
theorem monsterNortonOctadThreeUInput_actual (e : Fin 64) :
    Sum.elim monsterNortonPairHalfUPoolInput monsterNortonOctadThreeSupplementInput
      (monsterNortonOctadThreeUStorage e) = monsterNortonOctadThreeUInput e := by
  fin_cases e <;> rfl

/-- Every complete original code-three unit has its actual positive preferred U image. -/
theorem monsterNortonOctadThreeU_actual (e : Fin 64) :
    y555NortonActualU.val (monsterNortonPureShort (monsterNortonOctadThreeUInput e)) =
      monsterNortonPureShort (monsterNortonOctadThreeUOutput e) := by
  rw [← monsterNortonOctadThreeUInput_actual]
  unfold monsterNortonOctadThreeUOutput
  rcases h : monsterNortonOctadThreeUStorage e with k | k
  · exact monsterNortonPairHalfUPool_actual k
  · exact monsterNortonOctadThreeSupplement_actual k

/-- The full source-Q output is also identified, retaining every central phase. -/
theorem monsterNortonOctadThreeU_Q_image (e : Fin 64) :
    spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonOctadThreeUInput e)) =
        monsterNortonShortQ (monsterNortonOctadThreeUOutput e) := by
  rw [← monsterNortonOctadThreeUInput_actual]
  unfold monsterNortonOctadThreeUOutput
  rcases h : monsterNortonOctadThreeUStorage e with k | k
  · exact monsterNortonPairHalfUPool_Q_image k
  · exact monsterNortonOctadThreeSupplement_Q_image k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
