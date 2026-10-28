/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPermutationGenerationIncidenceData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPermutationGenerationRepresentatives

/-! Exact coordinate orbits of the genuine word14 and unordered-pair stabilizer chain. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual stabilizer images satisfy the independently certified incidence bounds. -/
theorem generatedFourth_permutation_image_eligible (k : Fin 7)
    (p : generatedFourthPermutationPointStabilizer k.val) :
    p.val.val (golayBasePoints k) ∈ generatedFourthPermutationEligible k := by
  apply generatedFourth_permutation_profile_separates
  intro r hr
  rw [← generatedFourth_permutation_profile_counts,
    ← generatedFourth_permutation_profile_counts, hr]
  exact (generatedFourth_permutation_incidence_invariant k.val p.val p.property _ _ _ _).symm

/-- The 45 genuine representatives cover each certified eligible coordinate set. -/
theorem generatedFourth_permutation_rep_covers : ∀ k : Fin 7, ∀ i : Fin 24,
    i ∈ generatedFourthPermutationEligible k →
      ∃ r : Fin 45, generatedFourthPermutationRepLevels r = k.val ∧
        (generatedFourthPermutationRep r).val (golayBasePoints k) = i := by
  intro k i hi
  have h : ∀ k : Fin 7, ∀ i : Fin 24,
      i ∈ generatedFourthPermutationEligible k →
        ∃ r : Fin 45, generatedFourthPermutationRepLevels r = k.val ∧
          generatedFourthPermutationRepImages r (golayBasePoints k) = i := by
    decide +kernel
  obtain ⟨r, hr, hri⟩ := h k i hi
  exact ⟨r, hr, (generatedFourth_permutation_rep_apply _ _).trans hri⟩

/-- Each genuine representative belongs to its stated prefix stabilizer. -/
theorem generatedFourth_permutation_rep_stabilizer (r : Fin 45) :
    generatedFourthPermutationRep r ∈
      generatedFourthPermutationPointStabilizer (generatedFourthPermutationRepLevels r) :=
  ⟨generatedFourth_permutation_four_le (generatedFourth_permutation_rep_mem r),
    generatedFourth_permutation_rep_prefix r⟩

/-- The actual coordinate orbit equals its certified eligible coordinate set. -/
theorem generatedFourth_permutation_orbit (k : Fin 7) :
    MulAction.orbit (generatedFourthPermutationPointStabilizer k.val) (golayBasePoints k) =
      {i | i ∈ generatedFourthPermutationEligible k} := by
  ext i
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨p, rfl⟩
    exact generatedFourth_permutation_image_eligible k p
  · intro hi
    obtain ⟨r, hr, hri⟩ := generatedFourth_permutation_rep_covers k i hi
    refine ⟨⟨generatedFourthPermutationRep r, ?_⟩, hri⟩
    simpa only [hr] using generatedFourth_permutation_rep_stabilizer r

/-- The actual orbit cardinalities are 16,15,6,1,4,2,1 on the faithful base. -/
theorem generatedFourth_permutation_orbit_card (k : Fin 7) :
    Nat.card (MulAction.orbit (generatedFourthPermutationPointStabilizer k.val)
      (golayBasePoints k)) = generatedFourthPermutationOrbitSizes k := by
  rw [generatedFourth_permutation_orbit, Nat.card_eq_fintype_card]
  change Fintype.card (generatedFourthPermutationEligible k) = _
  rw [Fintype.card_coe]
  exact generatedFourth_permutation_eligible_card k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
