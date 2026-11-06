/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full centralizer recognition in the actual constructed Griess group. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerLocalReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidualLocalEquality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every element of the full actual centralizer is in the constructed local group image. -/
theorem generatedCentralizer_element_local (g : generatedCentralizer) :
    ∃ h : H, g = generatedLocalIntoCentralizer h := by
  obtain ⟨h, hfix, hshort⟩ := generatedCentralizer_reduce_to_short_signs g
  obtain ⟨q, hq⟩ := generatedCentralizerTensorResidual_mem_localQ
    ((generatedLocalIntoCentralizer h)⁻¹ * g) hfix hshort
  refine ⟨h * inclQ q, ?_⟩
  calc
    g = generatedLocalIntoCentralizer h * ((generatedLocalIntoCentralizer h)⁻¹ * g) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    _ = generatedLocalIntoCentralizer h * generatedLocalIntoCentralizer (inclQ q) := by rw [hq]
    _ = generatedLocalIntoCentralizer (h * inclQ q) := (map_mul _ _ _).symm

/-- The centralizer of the actual central Q involution is exactly the actual local H image. -/
theorem generatedCentralizer_eq_local_range :
    Subgroup.centralizer {qIntoGenerated qCentralInvolution} = localIntoGenerated.range := by
  change generatedCentralizer = localIntoGenerated.range
  apply le_antisymm
  · intro g hg
    obtain ⟨h, hh⟩ := generatedCentralizer_element_local ⟨g, hg⟩
    exact ⟨h, (congrArg Subtype.val hh).symm⟩
  · exact localIntoGenerated_range_le_generatedCentralizer

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
