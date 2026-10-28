/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCorrectedWhole

/-! All three original constituents give the actual corrected Xi whole-axis fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The corrected original Xi fixes the entire genuine sixth axis with all preferred signs. -/
theorem generatedSixth_xi_full_fixed :
    rhoLocal (localFiberIntoH (generatedSixthCorrectedGenerator 4)) generatedSixthAxis =
      generatedSixthAxis :=
  generatedSixth_corrected_generator_full_fixed_of_blocks 4
    generatedSixth_xi_short_fixed generatedSixth_xi_tensor_fixed

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
