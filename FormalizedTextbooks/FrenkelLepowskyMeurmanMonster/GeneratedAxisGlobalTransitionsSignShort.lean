/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignQImage
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortBasis

/-! Preferred short phases and whole genuine source-sign transport from finite Q certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every preferred short phase is the explicit coefficient of the genuine source-sign Q image. -/
theorem generatedAxisGlobalSignLow_short_phase (a : Fin 2048) (r : GriessShortIndex) :
    localShortPhase (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0) r =
      toAdd (generatedAxisGlobalSignSpinImage a (griessShortQ r)).coeff := by
  unfold localShortPhase
  rw [generatedAxisGlobalSignLow_QImage]

/-- A complete finite Q certificate gives the entire signed short-unit image
of a low source sign. -/
theorem generatedAxisGlobalSignLow_short_basis (a : Fin 2048)
    (r s : GriessShortIndex) (c : ZMod 2)
    (hc : generatedAxisGlobalSignSpinImage a (griessShortQ r) =
      qCentral c * griessShortQ s) :
    (sourceGeneratedY (generatedAxisGlobalSignLowCode a) 0).val
        (griessConwayDecode (0, (Pi.single r 1, 0))) =
      griessConwayDecode (0, (qSign c • Pi.single s (1 : ℝ), 0)) := by
  rw [← generatedFifth_sign_local_generated, ← generatedFifth_sign_fiber_local]
  change localGriessRepresentation
    (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0) _ = _
  apply monsterNortonGriessShortBasis_of_Q_image
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq, generatedAxisGlobalSignLow_QImage]
  exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
