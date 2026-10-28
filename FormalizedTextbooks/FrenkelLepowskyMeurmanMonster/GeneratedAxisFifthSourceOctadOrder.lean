/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSourceOctadGeneration

/-! Actual pair orbit and pair stabilizer give the full source-octad permutation order. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- The actual pair stabilizer inside the octad group is the proved original flag group. -/
def generatedFifthSourceOctadPairStabilizerEquiv :
    MulAction.stabilizer generatedFifthSourceOctadSubgroup ({8, 11} : Finset (Fin 24)) ≃
      generatedFourthPermutationFlagStabilizer where
  toFun p := ⟨p.val.val, p.val.property,
    (generatedFifthSourceOctad_pair_fixed_iff p.val.val).mp p.property⟩
  invFun p := ⟨⟨p.val, p.property.1⟩,
    (generatedFifthSourceOctad_pair_fixed_iff p.val).mpr p.property.2⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := Subtype.ext rfl

/-- The full original octad group has precisely the 28 displayed unordered-pair images. -/
theorem generatedFifthSourceOctad_pair_orbit :
    MulAction.orbit generatedFifthSourceOctadSubgroup ({8, 11} : Finset (Fin 24)) =
      Set.range generatedFifthSourceOctadPair := by
  ext s
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨r, hr⟩ := generatedFifthSourceOctad_pair_transversal p.val p.property
    rw [generatedFifthSourceOctad_rep_pair] at hr
    exact ⟨r, hr⟩
  · rintro ⟨r, rfl⟩
    exact ⟨⟨generatedFifthSourceOctadPairRep r,
      generatedFifthSourceOctad_five_le (generatedFifthSourceOctad_rep_mem r)⟩,
      generatedFifthSourceOctad_rep_pair r⟩

/-- The actual original unordered-pair orbit has exactly 28 elements. -/
theorem generatedFifthSourceOctad_pair_orbit_card :
    Nat.card (MulAction.orbit generatedFifthSourceOctadSubgroup
      ({8, 11} : Finset (Fin 24))) = 28 := by
  rw [generatedFifthSourceOctad_pair_orbit,
    ← Nat.card_congr (Equiv.ofInjective generatedFifthSourceOctadPair
      generatedFifthSourceOctadPair_injective)]
  norm_num

/-- The genuine source-octad permutation stabilizer has order 322560. -/
theorem generatedFifthSourceOctad_card : Nat.card generatedFifthSourceOctadSubgroup = 322560 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    generatedFifthSourceOctadSubgroup ({8, 11} : Finset (Fin 24)))
  rw [Nat.card_prod, generatedFifthSourceOctad_pair_orbit_card,
    Nat.card_congr generatedFifthSourceOctadPairStabilizerEquiv,
    generatedFourth_permutation_flag_card] at h
  exact h.symm

/-- The five genuine original words generate a subgroup of exact order 322560. -/
theorem generatedFifthSourceOctad_five_card :
    Nat.card generatedFifthSourceOctadFiveSubgroup = 322560 := by
  rw [generatedFifthSourceOctad_five_eq, generatedFifthSourceOctad_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
