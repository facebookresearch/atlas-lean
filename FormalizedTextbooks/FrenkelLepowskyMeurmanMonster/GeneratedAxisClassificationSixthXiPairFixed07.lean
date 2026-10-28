/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairCertificate07

/-! Complete physical and preferred-phase certificates fix actual original short coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each checked original preferred output coordinate is fixed by the corrected full Xi action. -/
theorem generatedSixth_xi_pair_fixed07 (a : Fin 16) :
    let j : Fin 552 := ⟨112 + a.val, by omega⟩
    localShortOperator (generatedSixthCorrectedGenerator 4)
        (griessConwayEncode generatedSixthAxis).2.1 (generatedSixthXiPairOutput j) =
      (griessConwayEncode generatedSixthAxis).2.1 (generatedSixthXiPairOutput j) := by
  let j : Fin 552 := ⟨112 + a.val, by omega⟩
  have h := generatedSixth_xi_pair_certificate07 a
  change localShortOperator (generatedSixthCorrectedGenerator 4)
      (griessConwayEncode generatedSixthAxis).2.1 (generatedSixthXiPairOutput j) =
    (griessConwayEncode generatedSixthAxis).2.1 (generatedSixthXiPairOutput j)
  have hs : griessShortPermutation (generatedSixthRawGenerator 4).val.2
      (generatedSixthXiPairInput j) = generatedSixthXiPairOutput j := by
    apply generatedSixth_xi_short_permutation_of_integer _ _ (generatedSixthXiPairPhysicalPhase j)
    rw [generatedSixth_xi_pair_input_integral, generatedSixth_xi_pair_output_integral]
    exact h.2.2.1
  rw [generatedSixth_xi_short_direct_operator _ _ hs]
  apply generatedSixth_final_short_signed
  rw [generatedSixth_xi_pair_phase_soundness j h.1 h.2.1, h.2.2.2.1,
    generatedSixth_xi_pair_input_numerator, generatedSixth_xi_pair_output_numerator]
  exact h.2.2.2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
