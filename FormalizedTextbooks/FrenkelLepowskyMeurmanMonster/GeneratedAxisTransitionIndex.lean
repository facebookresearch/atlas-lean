/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionNormalizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaExact

/-! Identification and exact index of the actual triality transition subgroup. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The local preimage of the actual transition subgroup is the actual local Ω centralizer. -/
theorem generatedAxisTransitionNormalizer_comap_local :
    generatedAxisTransitionNormalizer.comap localIntoGenerated = localOmegaStabilizer := by
  ext h
  rw [Subgroup.mem_comap, generatedAxisTransitionNormalizer_eq_local_omega,
    Subgroup.mem_inf, localOmegaStabilizer, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have hr : localIntoGenerated h ∈ localIntoGenerated.range := ⟨h, rfl⟩
  simp only [hr, true_and]
  change localIntoGenerated h * localIntoGenerated (inclQ sourceOmegaQ) =
    localIntoGenerated (inclQ sourceOmegaQ) * localIntoGenerated h ↔ _
  rw [← map_mul, ← map_mul, localIntoGenerated_injective.eq_iff]

/-- The genuine source transition coset domain has exactly 16,584,750 elements. -/
theorem generatedAxisTransitionNormalizer_local_index :
    (generatedAxisTransitionNormalizer.comap localIntoGenerated).index = 16584750 := by
  rw [generatedAxisTransitionNormalizer_comap_local]
  exact localOmegaStabilizer_index

/-- The actual transition subgroup is precisely the embedded local Ω centralizer. -/
theorem generatedAxisTransitionNormalizer_eq_map_local :
    generatedAxisTransitionNormalizer = localOmegaStabilizer.map localIntoGenerated := by
  rw [← generatedAxisTransitionNormalizer_comap_local]
  symm
  apply Subgroup.map_comap_eq_self
  rw [generatedAxisTransitionNormalizer_eq_local_omega]
  exact inf_le_left

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
