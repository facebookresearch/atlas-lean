/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddressFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortSupportCompletion

/-! Exact sparse certificates supply signed source transport in the original short permutation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine mask and numerator certificates give the original signed source-image equality. -/
theorem generatedSixth_xi_short_address_signed (x y : GeneratedSixthXiShortAddress)
    (hm : sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortAddressMask x) = generatedSixthXiShortAddressMask y)
    (hn : nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMask x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y) :
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4)
        (generatedSixthXiShortAddressIndex x)) *
      (griessConwayEncode generatedSixthAxis).2.1 (generatedSixthXiShortAddressIndex x) =
    (griessConwayEncode generatedSixthAxis).2.1
      (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2
        (generatedSixthXiShortAddressIndex x)) := by
  have ha := congrArg (fun q : Q => Multiplicative.toAdd q.base)
    (generatedSixth_xi_short_address_Q x)
  have hb := congrArg (fun q : Q => Multiplicative.toAdd q.base)
    (generatedSixth_xi_short_address_Q y)
  have hs := generatedSixth_xi_short_permutation_of_binary _ _ _ _ ha hb hm
  rw [generatedSixth_corrected_generator_spatial, hs,
    generatedSixth_xi_short_selected_phase, generatedSixth_xi_short_address_Q,
    generatedSixth_xi_fast_mask_phase]
  apply generatedSixth_final_short_signed
  simpa only [generatedSixth_xi_short_address_numerator] using hn

/-- Signed equality at every genuinely nonzero source determines the entire actual short action. -/
theorem generatedSixth_xi_short_fixed_of_nonzero_sources
    (h : ∀ r : GriessShortIndex,
      (griessConwayEncode generatedSixthAxis).2.1 r ≠ 0 →
      qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
        (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r)) :
    localShortOperator (generatedSixthCorrectedGenerator 4)
        (griessConwayEncode generatedSixthAxis).2.1 =
      (griessConwayEncode generatedSixthAxis).2.1 := by
  have hw : ∀ r : GriessShortIndex,
      qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) ≠ 0 := by
    intro r hz
    have hh := qSign_sq (localShortPhase (generatedSixthCorrectedGenerator 4) r)
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hall := generatedSixth_xi_signed_support_complete
    (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2)
    (fun r => qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r))
    (griessConwayEncode generatedSixthAxis).2.1 hw h
  funext s
  obtain ⟨r, rfl⟩ :=
    (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2).surjective s
  rw [localShortOperator_image]
  exact hall r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
