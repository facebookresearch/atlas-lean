/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8SectionStabilizerCount

/-! Exact range-order assembly for a restriction representation of the actual Co0 E8 stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Any genuine representation of the actual E8 stabilizer with full positive pointwise
kernel 512 has image order 348364800. The identification of the representation kernel
with the actual pointwise group remains an explicit hypothesis. -/
theorem generatedTenth_e8_restriction_range_card {G : Type*} [Group G] (o : Fin 759)
    (f : generatedAxisE8SectionStabilizer (golayOctadWord o) →* G)
    (hk : Nat.card f.ker = 512) : Nat.card f.range = 348364800 := by
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker, hk, generatedAxisE8_sectionStabilizer_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
