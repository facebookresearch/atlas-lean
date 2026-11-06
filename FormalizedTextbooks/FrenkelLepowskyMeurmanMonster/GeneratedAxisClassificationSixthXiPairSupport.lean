/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairEnumeration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairScalarCache

/-! Every genuine pair coordinate occurs in the actual sixth-axis short support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
-- Check the complete signed cached original numerator, including its negative 27 entry.
/-- Every original pair-source numerator is nonzero. -/
theorem generatedSixth_xi_pair_input_numerator_ne_zero : ∀ j : Fin 552,
    generatedSixthXiPairInputNumerator j ≠ 0 := by
  have h : ∀ j : Fin 552, generatedSixthXiPairScalarInputNumerator j ≠ 0 := by
    decide +kernel
  simpa only [generatedSixth_xi_pair_scalar_input_numerator] using h

/-- Every genuine signed pair coordinate has nonzero coefficient in the actual sixth axis. -/
theorem generatedSixth_pair_short_nonzero (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedSixthAxis).2.1 (Sum.inl (s, p)) ≠ 0 := by
  obtain ⟨j, hj⟩ := generatedSixth_xi_pair_input_surjective s p
  rw [← hj, generatedSixth_final_short_numerator, generatedSixth_xi_pair_input_numerator]
  apply div_ne_zero
  · exact_mod_cast generatedSixth_xi_pair_input_numerator_ne_zero j
  · norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
