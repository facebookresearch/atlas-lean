/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSignLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSignGeneration

/-! Every actual equal-sign Conway class lifts to the full sixth-axis stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original source code with equal bits on the three root coordinates has an actual lift. -/
theorem generatedSixth_equal_sign_projected_mem (d : Fin 4096)
    (h17 : golayEncoder (golayLabelCoefficients d) 17 =
      golayEncoder (golayLabelCoefficients d) 16)
    (h19 : golayEncoder (golayLabelCoefficients d) 19 =
      golayEncoder (golayLabelCoefficients d) 16) :
    (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) ∈
      generatedSixthProjectedAxisStabilizer := by
  let K := generatedSixthProjectedAxisStabilizer.comap (QuotientGroup.mk' signsSubgroup)
  apply generatedSixth_source_sign_mem_of_generators K
    (fun j => generatedSixth_monomial_sign_projected_mem j) d h17 h19

/-- Every actual Golay code satisfying the three-coordinate sign condition lifts. -/
theorem generatedSixth_golay_equal_sign_projected_mem (c : golayCode)
    (h17 : c.val 17 = c.val 16) (h19 : c.val 19 = c.val 16) :
    (QuotientGroup.mk (golaySignIsometry c) : Co1) ∈ generatedSixthProjectedAxisStabilizer := by
  obtain ⟨d, hd⟩ := golayCodeEquiv.surjective c
  have hl := golayLabelCoefficients_bijective.surjective d
  obtain ⟨n, hn⟩ := hl
  have hc : sourceGeneratedSignCode n = c := by
    change golayEncoder.rangeRestrict (golayLabelCoefficients n) = c
    rw [hn]
    exact hd
  rw [← hc]
  apply generatedSixth_equal_sign_projected_mem n
  · change (sourceGeneratedSignCode n).val 17 = (sourceGeneratedSignCode n).val 16
    rw [hc]
    exact h17
  · change (sourceGeneratedSignCode n).val 19 = (sourceGeneratedSignCode n).val 16
    rw [hc]
    exact h19

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
