/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthQStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLocalSpatialProjection

/-! The genuine ninth local-axis projection retains the entire actual stabilizer
once Q fixes trivially. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The literal full-axis projection has trivial kernel, using the actual tensor Q exclusion. -/
theorem generatedNinthLocalAxisProjection_ker : generatedNinthLocalAxisProjection.ker = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro h hh
  have hp : projH h.val = 1 := hh
  have hr : h.val ∈ inclQ.range := by
    rw [inclQ_range_eq_projH_ker]
    exact hp
  obtain ⟨q, hq⟩ := hr
  have hf : rhoLocal (inclQ q) generatedNinthAxis = generatedNinthAxis := by
    rw [hq]
    exact h.property
  have he := generatedNinth_axis_Q_fixed_trivial q hf
  apply Subtype.ext
  rw [← hq, he, map_one]
  rfl

/-- The actual complete local-axis stabilizer embeds in its genuine Co1 image. -/
theorem generatedNinthLocalAxisProjection_injective :
    Function.Injective generatedNinthLocalAxisProjection := by
  intro a b hab
  have hk : a * b⁻¹ ∈ generatedNinthLocalAxisProjection.ker := by
    change generatedNinthLocalAxisProjection (a * b⁻¹) = 1
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  rw [generatedNinthLocalAxisProjection_ker, Subgroup.mem_bot] at hk
  exact mul_inv_eq_one.mp hk

/-- No extra kernel factor is lost in counting the actual projected full-axis stabilizer. -/
theorem generatedNinth_local_stabilizer_card_range :
    Nat.card generatedNinthLocalAxisStabilizer =
      Nat.card generatedNinthLocalAxisProjection.range := by
  have h := generatedNinthLocalAxisProjection.ker.card_mul_index
  rw [Subgroup.index_ker, generatedNinthLocalAxisProjection_ker, Subgroup.card_bot,
    one_mul] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
