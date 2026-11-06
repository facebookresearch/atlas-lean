/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialSpectrum

/-! The original binary action recognizes genuine short labels without choosing physical signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Checked preferred-Q masks and the actual original matrix
identify the true output short label. -/
theorem generatedSixth_xi_short_permutation_of_binary (r s : GriessShortIndex)
    (a b : ℕ)
    (ha : toAdd (griessShortQ r).base = monsterCo1GeometryBinaryMaskDecode a)
    (hb : toAdd (griessShortQ s).base = monsterCo1GeometryBinaryMaskDecode b)
    (h : sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) a = b) :
    griessShortPermutation (generatedSixthRawGenerator 4).val.2 r = s := by
  have hq := qBinaryAction_apply (spinConjugation (generatedSixthRawGenerator 4).val.1)
    (griessShortQ r)
  change spinBinaryAction (generatedSixthRawGenerator 4).val.1
    (toAdd (griessShortQ r).base) =
      toAdd (spinConjugation (generatedSixthRawGenerator 4).val.1 (griessShortQ r)).base at hq
  rw [(generatedSixthRawGenerator 4).property, ha] at hq
  have hm := sixthFrameOrbitOriginalGenerator_binary 14
    (monsterCo1GeometryBinaryMaskDecode a)
  change leechBinaryAction (generatedSixthRawGenerator 4).val.2
    (monsterCo1GeometryBinaryMaskDecode a) =
      sixthFrameOrbitColumnMatrix (sixthFrameOrbitColumns 14) *ᵥ
        monsterCo1GeometryBinaryMaskDecode a at hm
  rw [hm, ← sixthFrameOrbitMaskApply_decode, h] at hq
  have ht : (spinConjugation (generatedSixthRawGenerator 4).val.1
      (griessShortQ r)).base = (griessShortQ s).base :=
    toAdd.injective (hq.symm.trans hb.symm)
  exact griessShortQ_base_injective
    ((griessShortQ_image_base (generatedSixthRawGenerator 4) r).symm.trans ht)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
