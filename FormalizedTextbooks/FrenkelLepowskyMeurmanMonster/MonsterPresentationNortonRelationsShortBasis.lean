/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete signed short-basis transport from exact actual preferred-Q certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortLookup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A full preferred-Q image certificate identifies the entire signed short basis image. -/
theorem monsterNortonShortBasis_of_Q_image (f : localFiberSubgroup)
    (r s : GriessShortIndex) (c : ZMod 2)
    (h : spinConjugation f.val.1 (monsterNortonShortQ r) = qCentral c * monsterNortonShortQ s) :
    localShortOperator f (Pi.single r 1) = qSign c • (Pi.single s (1 : ℝ)) := by
  have hq := h
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq] at hq
  have hp : griessShortPermutation f.val.2 r = s := by
    apply griessShortClassEquiv.injective
    apply Subtype.ext
    apply leechHyperbolicCoordinates.injective
    have hb := congrArg (fun q : Q => toAdd q.base) hq
    rw [qCentral_mul_base, griessShortQ_image_base] at hb
    exact hb
  funext t
  by_cases ht : t = s
  · subst t
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] using
      monsterNortonShortOperator_of_Q_image f r s c h (Pi.single r 1)
  · have hd : (griessShortPermutation f.val.2).symm t ≠ r := by
      intro he
      have hh := congrArg (griessShortPermutation f.val.2) he
      rw [Equiv.apply_symm_apply, hp] at hh
      exact ht hh
    change qSign _ * ((Pi.single r (1 : ℝ) : GriessShortIndex → ℝ)
        ((griessShortPermutation f.val.2).symm t)) =
      qSign c * ((Pi.single s (1 : ℝ) : GriessShortIndex → ℝ) t)
    simp [hd, ht]

/-- The actual full local raw operator has the stated pure-short basis image. -/
theorem monsterNortonRawShortBasis_of_Q_image (f : localFiberSubgroup)
    (r s : GriessShortIndex) (c : ZMod 2)
    (h : spinConjugation f.val.1 (monsterNortonShortQ r) = qCentral c * monsterNortonShortQ s) :
    localConwayRawRepresentation f (0, (Pi.single r 1, 0)) =
      (0, (qSign c • Pi.single s (1 : ℝ), 0)) := by
  rw [localConwayRawRepresentation_apply]
  change (localMatrixRepresentation f 0,
    (localShortOperator f (Pi.single r 1), localTensorRepresentation f 0)) = _
  rw [map_zero, map_zero, monsterNortonShortBasis_of_Q_image f r s c h]

/-- Transported to the actual Griess space, the same finite certificate fixes the basis image. -/
theorem monsterNortonGriessShortBasis_of_Q_image (f : localFiberSubgroup)
    (r s : GriessShortIndex) (c : ZMod 2)
    (h : spinConjugation f.val.1 (monsterNortonShortQ r) = qCentral c * monsterNortonShortQ s) :
    localGriessRepresentation f (griessConwayDecode (0, (Pi.single r 1, 0))) =
      griessConwayDecode (0, (qSign c • Pi.single s (1 : ℝ), 0)) := by
  have he := localGriessRepresentation_encode f (griessConwayDecode (0, (Pi.single r 1, 0)))
  rw [griessConwayEncode_decode _ (by intro i j; rfl),
    monsterNortonRawShortBasis_of_Q_image f r s c h] at he
  have hd := congrArg griessConwayDecode he
  rw [griessConwayDecode_encode] at hd
  exact hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
