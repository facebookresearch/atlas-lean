/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual V phases of the two U images of every original pair. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsInverseUVProbe
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairsInverseSixth

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The lower-family U output has precisely the original family-zero V phase. -/
theorem monsterNortonEvenShortPairLowerOutputVPhase (k : Fin 11) :
    monsterNortonVShortPhase (monsterNortonEvenShortFirstUOutput ⟨k.val, by omega⟩) =
      monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩ := by
  have h := monsterNortonVPhase_forwardU
    (monsterNortonShortQ (monsterNortonEvenShortBasis ⟨k.val, by omega⟩))
  rw [monsterNortonEvenShortFirstU_Q_image, monsterNortonEvenShortPair_input] at h
  exact h.trans (monsterNortonInverseUVPairPolar_actual k 0)

/-- The upper-family U output has the same exact V phase, including the odd output. -/
theorem monsterNortonEvenShortPairUpperOutputVPhase (k : Fin 11) :
    monsterNortonVShortPhase (monsterNortonEvenShortUpperUOutput k) =
      monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩ := by
  have h := monsterNortonVPhase_forwardU
    (monsterNortonShortQ (monsterNortonEvenShortUpperInput k))
  rw [monsterNortonEvenShortUpperU_Q_image] at h
  exact h.trans (monsterNortonInverseUVPairPolar_actual k 1)

/-- The normalized full sixth inverse packet retains every matrix, short and tensor coordinate. -/
noncomputable def monsterNortonEvenShortPairsInverseSixthNormalized
    (k : Fin 11) (s : Fin 2) : GriessSpace :=
  (qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2) •
    griessConwayDecode (Matrix.diagonal (fun i => monsterNortonEvenShortPairsUMatrix k i i),
      (monsterNortonMatrixTrialityShort (monsterNortonEvenShortPairsUMatrix k), 0)) +
    (monsterNortonPairFamilySign s *
      qSign (monsterNortonEvenShortInitialVPhase ⟨k.val, by omega⟩) / 2) •
      (monsterNortonShortExtraPacket (monsterNortonEvenShortFirstUOutput ⟨k.val, by omega⟩) +
        monsterNortonShortExtraPacket (monsterNortonEvenShortUpperUOutput k))

/-- The normalized packet follows from true phase transport, with no discarded odd branch. -/
theorem monsterNortonEvenShortPairsInverseSixth_normalized (k : Fin 11) (s : Fin 2) :
    monsterNortonEvenShortPairsInverseSixth k s =
      monsterNortonEvenShortPairsInverseSixthNormalized k s := by
  unfold monsterNortonEvenShortPairsInverseSixth
    monsterNortonEvenShortPairsInverseSixthNormalized
  rw [monsterNortonEvenShortPairLowerOutputVPhase,
    monsterNortonEvenShortPairUpperOutputVPhase, ← smul_add, smul_smul]
  congr 2
  ring

/-- Both literal inverse words have the complete normalized sixth image on all original pairs. -/
theorem monsterNortonEvenShortPairsInverseFirstSix_normalized (k : Fin 11) (s : Fin 2) :
    sExtra (y555NortonV.val (y555NortonActualU.val (y555NortonV.val (sExtra.symm
      (y555NortonV.val
        (monsterNortonPureShort (Sum.inl (s, monsterNortonEvenShortPairIndex k)))))))) =
      monsterNortonEvenShortPairsInverseSixthNormalized k s := by
  rw [monsterNortonEvenShortPairsInverseFirstSix_actual,
    monsterNortonEvenShortPairsInverseSixth_normalized]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
