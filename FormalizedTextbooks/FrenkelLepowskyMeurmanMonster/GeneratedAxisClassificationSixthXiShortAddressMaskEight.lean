/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddressSigned
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOctadMaskEight

/-! Eight-coordinate octad masks retain the full original preferred action on sparse sources. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sparse masks use exactly the genuine eight octad contributors and unchanged other families. -/
def generatedSixthXiShortAddressMaskEight : GeneratedSixthXiShortAddress → ℕ
  | Sum.inr (Sum.inl (f, e)) => generatedSixthXiOctadMaskEight f e
  | x => generatedSixthXiShortAddressMask x

/-- Every accelerated mask is the complete actual preferred lift, including its central bit. -/
theorem generatedSixth_xi_short_address_mask_eight_Q (x : GeneratedSixthXiShortAddress) :
    griessShortQ (generatedSixthXiShortAddressIndex x) =
      generatedSixthXiMaskQ (generatedSixthXiShortAddressMaskEight x) := by
  rcases x with j | (⟨f, e⟩ | ⟨f, j⟩)
  · exact generatedSixth_xi_short_address_Q (Sum.inl j)
  · exact generatedSixth_xi_octad_mask_eight_Q f e
  · exact generatedSixth_xi_short_address_Q (Sum.inr (Sum.inr (f, j)))

/-- Full binary and signed coefficient checks retain the genuine original source-image action. -/
theorem generatedSixth_xi_short_address_mask_eight_signed (x y : GeneratedSixthXiShortAddress)
    (hm : sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortAddressMaskEight x) = generatedSixthXiShortAddressMaskEight y)
    (hn : nortonUIntegerSign (generatedSixthXiFastMaskPhase
        (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y) :
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4)
        (generatedSixthXiShortAddressIndex x)) *
      (griessConwayEncode generatedSixthAxis).2.1 (generatedSixthXiShortAddressIndex x) =
    (griessConwayEncode generatedSixthAxis).2.1
      (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2
        (generatedSixthXiShortAddressIndex x)) := by
  have ha := congrArg (fun q : Q => Multiplicative.toAdd q.base)
    (generatedSixth_xi_short_address_mask_eight_Q x)
  have hb := congrArg (fun q : Q => Multiplicative.toAdd q.base)
    (generatedSixth_xi_short_address_mask_eight_Q y)
  have hs := generatedSixth_xi_short_permutation_of_binary _ _ _ _ ha hb hm
  rw [generatedSixth_corrected_generator_spatial, hs,
    generatedSixth_xi_short_selected_phase, generatedSixth_xi_short_address_mask_eight_Q,
    generatedSixth_xi_fast_mask_phase]
  apply generatedSixth_final_short_signed
  simpa only [generatedSixth_xi_short_address_numerator] using hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
