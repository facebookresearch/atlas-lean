/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiBinaryShortTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFastMaskPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalShortNumerator

/-! Genuine masks, full original phases and signed integer coefficients certify short fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Complete preferred-Q and signed-numerator checks give the genuine corrected Xi short action. -/
theorem generatedSixth_xi_short_fixed_of_mask_certificate (r s : GriessShortIndex)
    (a b : ℕ)
    (ha : griessShortQ r = generatedSixthXiMaskQ a)
    (hb : griessShortQ s = generatedSixthXiMaskQ b)
    (hM : sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) a = b)
    (hn : nortonUIntegerSign (generatedSixthXiFastMaskPhase a) *
      generatedSixthFinalShortNumerator r = generatedSixthFinalShortNumerator s) :
    localShortOperator (generatedSixthCorrectedGenerator 4)
      (griessConwayEncode generatedSixthAxis).2.1 s =
        (griessConwayEncode generatedSixthAxis).2.1 s := by
  have hqa : Multiplicative.toAdd (griessShortQ r).base =
      monsterCo1GeometryBinaryMaskDecode a := by rw [ha]; rfl
  have hqb : Multiplicative.toAdd (griessShortQ s).base =
      monsterCo1GeometryBinaryMaskDecode b := by rw [hb]; rfl
  have hs := generatedSixth_xi_short_permutation_of_binary r s a b hqa hqb hM
  rw [generatedSixth_xi_short_selected_operator _ _ hs, ha,
    generatedSixth_xi_fast_mask_phase]
  exact generatedSixth_final_short_signed r s _ hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
