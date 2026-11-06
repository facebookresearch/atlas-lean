/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSelectedTripleData

/-! The full genuine octad permutation group has 56 triple images and stabilizer order 5760. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- Exact physical support of the selected original octad. -/
def generatedSeventhSelectedOctadSupport : Finset (Fin 24) := {0, 1, 2, 3, 16, 17, 18, 19}

/-- The literal support agrees with the genuine selected Golay codeword. -/
theorem generatedSeventh_selected_octad_support (i : Fin 24) :
    i ∈ generatedSeventhSelectedOctadSupport ↔ golayOctadWord generatedFifthFlagOctad i ≠ 0 := by
  rw [generatedFifth_flag_word_coordinate]
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 4000000 in
-- Only the 24^3 triples of physical coordinates are inspected.
/-- Every distinct triple in the selected octad has one of the 56 genuine addresses. -/
theorem generatedSeventh_selected_triple_covers : ∀ a b c : Fin 24,
    a ∈ generatedSeventhSelectedOctadSupport → b ∈ generatedSeventhSelectedOctadSupport →
      c ∈ generatedSeventhSelectedOctadSupport → a ≠ b → a ≠ c → b ≠ c →
        ∃ k : Fin 56, ({a, b, c} : Finset (Fin 24)) = generatedSeventhSelectedTriple k := by
  decide +kernel

/-- Every full selected-octad permutation preserves the original physical support. -/
theorem generatedSeventh_selected_octad_image_mem (p : generatedFifthSelectedOctadSubgroup)
    (i : Fin 24) (hi : i ∈ generatedSeventhSelectedOctadSupport) :
    p.val.val i ∈ generatedSeventhSelectedOctadSupport := by
  rw [generatedSeventh_selected_octad_support] at hi ⊢
  have hp := congrFun ((generatedFifthSelectedOctadSubgroup_mem p.val).mp p.property) (p.val.val i)
  change golayOctadWord generatedFifthFlagOctad (p.val.val.symm (p.val.val i)) =
    golayOctadWord generatedFifthFlagOctad (p.val.val i) at hp
  rw [p.val.val.symm_apply_apply] at hp
  rwa [← hp]

/-- The full genuine selected-octad orbit is exactly the 56 displayed physical triples. -/
theorem generatedSeventh_selected_triple_orbit :
    MulAction.orbit generatedFifthSelectedOctadSubgroup ({16, 17, 19} : Finset (Fin 24)) =
      Set.range generatedSeventhSelectedTriple := by
  ext s
  constructor
  · rintro ⟨p, rfl⟩
    have hc : (p • ({16, 17, 19} : Finset (Fin 24))).card = 3 := by
      change (Finset.image p.val.val ({16, 17, 19} : Finset (Fin 24))).card = 3
      rw [Finset.card_image_of_injective _ p.val.val.injective]
      decide +kernel
    obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.mp hc
    have hs : ∀ i ∈ p • ({16, 17, 19} : Finset (Fin 24)),
        i ∈ generatedSeventhSelectedOctadSupport := by
      intro i hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_smul_finset.mp hi
      subst i
      apply generatedSeventh_selected_octad_image_mem p j
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl <;> decide +kernel
    have ha := hs a (by rw [he]; simp)
    have hb := hs b (by rw [he]; simp)
    have hc' := hs c (by rw [he]; simp)
    obtain ⟨k, hk⟩ := generatedSeventh_selected_triple_covers a b c ha hb hc' hab hac hbc
    exact ⟨k, hk.symm.trans he.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨generatedSeventhSelectedTripleRep k, generatedSeventh_selected_triple_rep_mem k⟩,
      generatedSeventh_selected_triple_rep_image k⟩

/-- There are exactly 56 genuine triple images under the full actual octad subgroup. -/
theorem generatedSeventh_selected_triple_orbit_card :
    Nat.card (MulAction.orbit generatedFifthSelectedOctadSubgroup
      ({16, 17, 19} : Finset (Fin 24))) = 56 := by
  rw [generatedSeventh_selected_triple_orbit,
    ← Nat.card_congr (Equiv.ofInjective generatedSeventhSelectedTriple
      generatedSeventh_selected_triple_injective)]
  norm_num

/-- The actual selected-octad permutation subgroup preserving the triangle has order 5760. -/
theorem generatedSeventh_selected_triple_stabilizer_card :
    Nat.card (MulAction.stabilizer generatedFifthSelectedOctadSubgroup
      ({16, 17, 19} : Finset (Fin 24))) = 5760 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    generatedFifthSelectedOctadSubgroup ({16, 17, 19} : Finset (Fin 24)))
  rw [Nat.card_prod, generatedSeventh_selected_triple_orbit_card,
    generatedFifthSelectedOctad_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
