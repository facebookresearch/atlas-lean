/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual Norton short-basis transport from finite source-coordinate certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCacheInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A finite full-phase certificate gives the entire actual Norton image of a pure-short vector. -/
theorem monsterNortonU_short_basis_of_source_certificate (r s : GriessShortIndex)
    (c : ZMod 2)
    (hc : monsterNortonUQFastImage (monsterNortonShortQSource r) =
      qCentral c * monsterNortonShortQSource s) :
    y555NortonActualU.val (griessConwayDecode (0, (Pi.single r 1, 0))) =
      griessConwayDecode (0, (qSign c • Pi.single s 1, 0)) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (griessConwayDecode (0, (Pi.single r 1, 0))) = _
  apply monsterNortonGriessShortBasis_of_Q_image
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq]
  rw [monsterNortonShortQSource_actual, monsterNortonShortQSource_actual] at hc
  rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq]
  exact hc

/-- The inverse full-phase cache gives the entire actual inverse Norton short-basis image. -/
theorem monsterNortonU_inverse_short_basis_of_source_certificate (r s : GriessShortIndex)
    (c : ZMod 2)
    (hc : monsterNortonUQInverseFastImage (monsterNortonShortQSource r) =
      qCentral c * monsterNortonShortQSource s) :
    (y555NortonActualU⁻¹).val (griessConwayDecode (0, (Pi.single r 1, 0))) =
      griessConwayDecode (0, (qSign c • Pi.single s 1, 0)) := by
  rw [← monsterNortonULocal_generated, ← map_inv]
  change localGriessRepresentation (monsterNortonUFiber⁻¹)
    (griessConwayDecode (0, (Pi.single r 1, 0))) = _
  apply monsterNortonGriessShortBasis_of_Q_image
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq]
  rw [monsterNortonShortQSource_actual, monsterNortonShortQSource_actual] at hc
  rw [monsterNortonUQInverseFastImage_eq]
  exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
