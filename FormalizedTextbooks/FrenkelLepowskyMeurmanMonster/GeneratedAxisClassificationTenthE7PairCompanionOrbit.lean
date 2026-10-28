/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7PairPermutationGroup

/-! The entire actual pair group has precisely the original sixteen-companion orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine pair permutation preserves positivity on both complete first-pair coordinates. -/
theorem generatedTenth_e7_pair_mask_first (p : generatedTenthE7PairPermutationGroup)
    (d : Fin 4096) (hd0 : (golayEncodedMask d.val).testBit 0 = true)
    (hd1 : (golayEncodedMask d.val).testBit 1 = true) (i : Fin 2) :
    (golayEncodedMask (golayLabelPermutation p.val.val d).val).testBit i.val = true := by
  let k : Fin 24 := Fin.castAdd 22 i
  have h := congrFun (golayLabelPermutation_word p.val.val d) k
  change golayEncoder (golayLabelCoefficients (golayLabelPermutation p.val.val d)) k =
    golayEncoder (golayLabelCoefficients d) (p.val.val.val.symm k) at h
  have hv := congrArg ZMod.val h
  rw [golayLabelEncoder_match, golayLabelEncoder_match] at hv
  have hk := generatedTenth_e7_pair_permutation_coordinate p⁻¹ i
  change p.val.val.val.symm k = 0 ∨ p.val.val.val.symm k = 1 at hk
  have hone :
      (if (golayEncodedMask d.val).testBit (p.val.val.val.symm k).val = true then
        (1 : ℕ) else 0) = 1 := by
    rcases hk with hk | hk
    · rw [hk, show (0 : Fin 24).val = 0 by decide +kernel]
      exact ite_eq_left hd0
    · rw [hk, show (1 : Fin 24).val = 1 by decide +kernel]
      exact ite_eq_left hd1
  rw [hone] at hv
  change (if (golayEncodedMask (golayLabelPermutation p.val.val d).val).testBit i.val = true
    then (1 : ℕ) else 0) = 1 at hv
  by_contra hn
  rw [ite_eq_right hn] at hv
  omega

/-- Every actual whole pair-group companion orbit member lies in the original incident sector. -/
theorem generatedTenth_e7_pair_companion_orbit_subset :
    MulAction.orbit generatedTenthE7PairPermutationGroup (2306 : Fin 4096) ⊆
      (generatedFeasibleContainingSelectedIncidentCodes 0 : Set (Fin 4096)) := by
  rintro d ⟨p, rfl⟩
  change golayLabelPermutation p.val.val 2306 ∈ generatedFeasibleContainingSelectedIncidentCodes 0
  have ha := generatedTenth_e7_companion_incident_actual
  simp only [generatedFeasibleContainingSelectedIncidentCodes, Finset.mem_filter] at ha ⊢
  refine ⟨(golayLabelPermutation_octad p.val.val 2306).mpr ha.1, ?_⟩
  refine ⟨⟨generatedTenth_e7_pair_mask_first p 2306 ha.2.1.1 ha.2.1.2 0,
    generatedTenth_e7_pair_mask_first p 2306 ha.2.1.1 ha.2.1.2 1⟩, ?_⟩
  rw [generatedTenth_e7_companion_selected_invariant p.val]
  exact ha.2.2

/-- The entire genuine pair group has exactly the complete original sixteen-code orbit. -/
theorem generatedTenth_e7_pair_companion_orbit_actual :
    MulAction.orbit generatedTenthE7PairPermutationGroup (2306 : Fin 4096) =
      (generatedFeasibleContainingSelectedIncidentCodes 0 : Set (Fin 4096)) := by
  apply Set.Subset.antisymm generatedTenth_e7_pair_companion_orbit_subset
  rw [← generatedTenth_e7_companion_pointwise_orbit_actual]
  exact generatedTenth_e7_pointwise_companion_orbit_le_pair

/-- The actual whole pair-group companion orbit has cardinality16, without an orbit premise. -/
theorem generatedTenth_e7_pair_companion_orbit_card :
    Nat.card (MulAction.orbit generatedTenthE7PairPermutationGroup (2306 : Fin 4096)) = 16 := by
  rw [generatedTenth_e7_pair_companion_orbit_actual, generatedTenth_e7_companion_sector_card]

/-- The entire actual octad, unordered-pair, and companion permutation stabilizer has order720. -/
theorem generatedTenth_e7_pair_companion_stabilizer_card :
    Nat.card (MulAction.stabilizer generatedTenthE7PairPermutationGroup (2306 : Fin 4096)) =
      720 := by
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup generatedTenthE7PairPermutationGroup
      (2306 : Fin 4096))
  rw [Nat.card_prod, generatedTenth_e7_pair_companion_orbit_card,
    generatedTenth_e7_pair_permutation_group_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
