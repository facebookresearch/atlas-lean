/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQDiagonalRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQPermutationSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQSignProjection

/-! Actual full-axis lifts contain the genuine code signs and coordinate-flag permutations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine code-sign quotient belongs to the complete-axis projection. -/
theorem generatedEighth_projected_code_sign_mem (c : golayCode) :
    (QuotientGroup.mk (golaySignIsometry c) : Co1) ∈ generatedEighthProjectedAxisStabilizer := by
  obtain ⟨a, ha⟩ := c.property
  obtain ⟨d, hd⟩ := golayLabelCoefficients_bijective.surjective a
  have hc : c = sourceGeneratedSignCode d := by
    apply Subtype.ext
    change c.val = golayEncoder (golayLabelCoefficients d)
    rw [hd, ha]
  rw [hc]
  exact generatedEighth_projected_source_sign_mem d

/-- Every genuine coordinate-flag permutation has its quotient in the full-axis projection. -/
theorem generatedEighth_projected_flag_permutation_mem (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedEighthPermutationFlagStabilizer) :
    (QuotientGroup.mk (golayPermutationIsometry p) : Co1) ∈
      generatedEighthProjectedAxisStabilizer := by
  obtain ⟨c, hc⟩ := generatedEighth_flag_permutation_signed_unit p hp
  let g := golayMonomialPair (c, p)
  have hm : g ∈ golayMonomialSubgroup := ⟨c, p, rfl⟩
  obtain ⟨f, hs, hf, ho⟩ := generatedEighth_middle_monomial_line_lift g hm hc
  obtain ⟨h, ha, hh⟩ := generatedEighth_middle_omega_forward_lift f hf ho
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH k = h at hk
  have hak : rhoLocal (localFiberIntoH k) =
      sExtra * rhoLocal (localFiberIntoH f) * sExtra⁻¹ := by rw [hk]; exact ha
  have hd := generatedEighth_forward_diagonal_action f k c p hs hak
  obtain ⟨b, hb⟩ := generatedEighth_diagonal_recognizes_permutation k.val.2 p hd
  have hhmem : projH h ∈ generatedEighthProjectedAxisStabilizer := ⟨⟨h, hh⟩, rfl⟩
  rw [← hk] at hhmem
  change (QuotientGroup.mk' signsSubgroup) k.val.2 ∈ generatedEighthProjectedAxisStabilizer at hhmem
  rw [hb, map_mul] at hhmem
  change (QuotientGroup.mk (golaySignIsometry b) : Co1) *
    (QuotientGroup.mk (golayPermutationIsometry p) : Co1) ∈
      generatedEighthProjectedAxisStabilizer at hhmem
  have hsign := generatedEighth_projected_code_sign_mem b
  have hprod := generatedEighthProjectedAxisStabilizer.mul_mem
    (generatedEighthProjectedAxisStabilizer.inv_mem hsign) hhmem
  simpa only [← mul_assoc, inv_mul_cancel, one_mul] using hprod

/-- Every actual spatial matrix stabilizer maps into the complete-axis projection. -/
theorem generatedEighth_spatial_quotient_mem (g : leechIsomSubgroup)
    (hg : g ∈ generatedEighthSpatialStabilizer) :
    (QuotientGroup.mk (g) : Co1) ∈ generatedEighthProjectedAxisStabilizer := by
  have hm := generatedEighthSpatialStabilizer_le_monomial hg
  obtain ⟨c, p, he⟩ := hm
  have hp : p ∈ generatedEighthPermutationFlagStabilizer := by
    have hs := hg
    rw [he] at hs
    exact (generatedEighth_monomial_matrix_fix_iff c p).mp hs
  change (QuotientGroup.mk' signsSubgroup) g ∈
    generatedEighthProjectedAxisStabilizer
  rw [he, map_mul]
  exact generatedEighthProjectedAxisStabilizer.mul_mem
    (generatedEighth_projected_code_sign_mem c)
    (generatedEighth_projected_flag_permutation_mem p hp)

/-- The entire actual full-axis projection equals the proved genuine spatial stabilizer. -/
theorem generatedEighth_projected_stabilizer_eq_spatial :
    generatedEighthProjectedAxisStabilizer = generatedEighthCo1SpatialStabilizer := by
  apply le_antisymm generatedEighthProjectedAxisStabilizer_le_spatial
  rintro c ⟨g, hg, rfl⟩
  exact generatedEighth_spatial_quotient_mem g hg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
