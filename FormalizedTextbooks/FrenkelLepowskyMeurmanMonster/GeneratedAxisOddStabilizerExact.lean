/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddStabilizerProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddLocalLift

/-! Exact projected lifting and the full actual odd-axis stabilizer order. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine spatial line-stabilizer lifts make the restricted actual H projection onto. -/
theorem generatedOddLocalAxisProjection_surjective :
    Function.Surjective generatedOddLocalAxisProjection := by
  intro a
  obtain ⟨g, hg, hga⟩ := a.property
  obtain ⟨f, hfg, hfix⟩ := generatedOddAxis_projected_stabilizer_lift g hg
  refine ⟨⟨localFiberIntoH f, hfix⟩, Subtype.ext ?_⟩
  change projH (localFiberIntoH f) = a.val
  change QuotientGroup.mk' signsSubgroup f.val.2 = a.val
  rw [hfg]
  exact hga

/-- The genuine odd-axis H stabilizer has order 85571854663680. -/
theorem generatedOddLocalAxisStabilizer_card :
    Nat.card generatedOddLocalAxisStabilizer = 85571854663680 := by
  have h := generatedOddLocalAxisProjection.ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr generatedOddLocalAxisProjection_surjective,
    Subgroup.card_top, generatedOddLocalAxisProjection_kernel_card,
    generatedNormEightCo1LineStabilizer_card] at h
  norm_num at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
