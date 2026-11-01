/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddresses
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortMaskFixed

/-! Sparse certificates give the actual whole preferred-short action at each transported output. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Exact sparse binary transport and full signed numerators certify original Xi fixation. -/
theorem generatedSixth_xi_short_address_fixed (x y : GeneratedSixthXiShortAddress)
    (hm : sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortAddressMask x) = generatedSixthXiShortAddressMask y)
    (hn : nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMask x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y) :
    localShortOperator (generatedSixthCorrectedGenerator 4)
        (griessConwayEncode generatedSixthAxis).2.1 (generatedSixthXiShortAddressIndex y) =
      (griessConwayEncode generatedSixthAxis).2.1 (generatedSixthXiShortAddressIndex y) := by
  apply generatedSixth_xi_short_fixed_of_mask_certificate
    (generatedSixthXiShortAddressIndex x) _
    (generatedSixthXiShortAddressMask x) (generatedSixthXiShortAddressMask y)
    (generatedSixth_xi_short_address_Q x) (generatedSixth_xi_short_address_Q y) hm
  simpa only [generatedSixth_xi_short_address_numerator] using hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
