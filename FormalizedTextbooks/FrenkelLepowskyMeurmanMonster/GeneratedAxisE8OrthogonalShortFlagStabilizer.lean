/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8OrthogonalShortReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagStabilizer

/-! Actual orthogonal section-short-line transitivity and the genuine outside flag stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Genuine lattice maps transport orthogonality of actual preferred integral roots. -/
theorem generatedAxisE8OrthogonalShortLines_image (g : leechIsomSubgroup)
    (S : Submodule ℤ leechIntegral) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8OrthogonalShortLines S) :
    griessShortPermutation g r ∈
      generatedAxisE8OrthogonalShortLines (S.map (leechIntegralAction g).toLinearMap) := by
  rintro u ⟨v, hv, hgu⟩
  change leechIntegralAction g v = u at hgu
  have hp := leechRootedA2_integral_pairing_action g (griessShortLatticeVector r) v
  have hz := hr v hv
  change leechIntegralPairing (griessShortLatticeVector r).val v.val = 0 at hz
  rw [hz, hgu] at hp
  rcases generatedE8Short_integral_sign g r with he | he
  · rw [he] at hp
    exact hp
  · rw [he] at hp
    simp only [Submodule.coe_neg, leechIntegralPairing, Pi.neg_apply,
      neg_mul, Finset.sum_neg_distrib, neg_eq_zero] at hp
    exact hp

/-- Inverses of actual old-section-preserving words preserve that same section. -/
theorem generatedAxisE8Orthogonal_preserves_inv (g : leechIsomSubgroup)
    (hg : generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) g) :
    generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) g⁻¹ := by
  intro u
  have h := hg (leechIntegralAction g⁻¹ u)
  have he : leechIntegralAction g (leechIntegralAction g⁻¹ u) = u := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [he] at h
  exact h.symm

/-- All4320 genuine signed orthogonal roots are conjugate by original section-preserving words. -/
theorem generatedAxisE8Orthogonal_signed_transitive (u v : leechIntegral)
    (hu : u ∈ generatedAxisE8OrthogonalSignedRoots)
    (hv : v ∈ generatedAxisE8OrthogonalSignedRoots) :
    ∃ g : leechIsomSubgroup, g ∈ leechConcreteGeneratorSubgroup ∧
      generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad) g ∧
      leechIntegralAction g u = v := by
  obtain ⟨a, ha, hap, hau⟩ := generatedAxisE8Orthogonal_short_reduction u hu
  obtain ⟨b, hb, hbp, hbv⟩ := generatedAxisE8Orthogonal_short_reduction v hv
  refine ⟨b⁻¹ * a, leechConcreteGeneratorSubgroup.mul_mem
    (leechConcreteGeneratorSubgroup.inv_mem hb) ha,
    generatedAxisE8Orthogonal_preserves_mul _ _
      (generatedAxisE8Orthogonal_preserves_inv b hbp) hap, ?_⟩
  apply (leechIntegralAction b).injective
  rw [← LinearEquiv.mul_apply, ← map_mul]
  have hmul : b * (b⁻¹ * a) = a := by group
  rw [hmul]
  exact Subtype.ext (hau.trans hbv.symm)

/-- All2160 genuine preferred orthogonal roots are in one actual full section-group orbit. -/
theorem generatedAxisE8Orthogonal_preferred_transitive (r s : GriessShortIndex)
    (hr : r ∈ generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)))
    (hs : s ∈ generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))) :
    ∃ g : generatedAxisE8SectionStabilizer (golayOctadWord generatedOctadBasisOctad),
      griessShortPermutation g.val r = s := by
  obtain ⟨g, _, hgp, hgr⟩ := generatedAxisE8Orthogonal_signed_transitive
    (griessShortLatticeVector r) (griessShortLatticeVector s)
    ⟨griessShortIntegral_squareSum r, (generatedAxisE8Orthogonal_old_mem r).mp hr⟩
    ⟨griessShortIntegral_squareSum s, (generatedAxisE8Orthogonal_old_mem s).mp hs⟩
  refine ⟨⟨g, (generatedAxisE8SectionStabilizer_mem _ _).mpr
    (generatedAxisE8_preserving_image _ _ hgp)⟩, ?_⟩
  exact (leechRootedA2_short_perm_eq_iff g r s).mpr (Or.inl hgr)

/-- The original fixed first root is genuinely orthogonal to the original old octad section. -/
theorem generatedAxisE8Orthogonal_first_mem :
    Sum.inl (0, generatedFeasiblePhysicalRootPair) ∈ generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) := by
  rw [generatedAxisE8Orthogonal_pair_mem, generatedFeasiblePhysicalRootPair_coordinates]
  decide +kernel

/-- The full original section-group orbit of the actual first root is exactly the complement. -/
theorem generatedAxisE8Orthogonal_first_orbit :
    MulAction.orbit (generatedAxisE8SectionStabilizer (golayOctadWord generatedOctadBasisOctad))
      (Sum.inl (0, generatedFeasiblePhysicalRootPair) : GriessShortIndex) =
    generatedAxisE8OrthogonalShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)) := by
  ext r
  constructor
  · rintro ⟨g, rfl⟩
    have hr := generatedAxisE8OrthogonalShortLines_image g.val
      (generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad))
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) generatedAxisE8Orthogonal_first_mem
    have hs := (generatedAxisE8SectionStabilizer_mem _ _).mp g.property
    change generatedAxisE8ImageSection g.val _ = _ at hs
    change griessShortPermutation g.val _ ∈ _
    rwa [← hs]
  · intro hr
    obtain ⟨g, hg⟩ := generatedAxisE8Orthogonal_preferred_transitive _ _
      generatedAxisE8Orthogonal_first_mem hr
    exact ⟨g, hg⟩

/-- The actual first-root stabilizer inside the actual original section group has order82575360. -/
theorem generatedAxisE8Orthogonal_section_point_stabilizer_card :
    Nat.card (MulAction.stabilizer
      (generatedAxisE8SectionStabilizer (golayOctadWord generatedOctadBasisOctad))
      (Sum.inl (0, generatedFeasiblePhysicalRootPair) : GriessShortIndex)) = 82575360 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite
    (generatedAxisE8SectionStabilizer (golayOctadWord generatedOctadBasisOctad))
  let _ := Fintype.ofFinite (MulAction.stabilizer
    (generatedAxisE8SectionStabilizer (golayOctadWord generatedOctadBasisOctad))
    (Sum.inl (0, generatedFeasiblePhysicalRootPair) : GriessShortIndex))
  let _ := Fintype.ofFinite (MulAction.orbit
    (generatedAxisE8SectionStabilizer (golayOctadWord generatedOctadBasisOctad))
    (Sum.inl (0, generatedFeasiblePhysicalRootPair) : GriessShortIndex))
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (generatedAxisE8SectionStabilizer (golayOctadWord generatedOctadBasisOctad))
    (Sum.inl (0, generatedFeasiblePhysicalRootPair) : GriessShortIndex)
  simp only [← Nat.card_eq_fintype_card] at h
  rw [generatedAxisE8Orthogonal_first_orbit, generatedAxisE8Orthogonal_short_lines_card,
    generatedAxisE8_sectionStabilizer_card] at h
  omega

/-- The full genuine outside section/short flag group is the nested actual point stabilizer. -/
def generatedAxisE8OrthogonalFlagEquiv :
    generatedAxisE8ShortFlagStabilizer generatedOctadBasisOctad
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ≃
      MulAction.stabilizer
        (generatedAxisE8SectionStabilizer (golayOctadWord generatedOctadBasisOctad))
        (Sum.inl (0, generatedFeasiblePhysicalRootPair) : GriessShortIndex) where
  toFun g := ⟨⟨g.val, (generatedAxisE8SectionStabilizer_mem _ _).mpr
    ((generatedAxisE8ShortFlagStabilizer_mem _ _ _).mp g.property).1⟩,
    ((generatedAxisE8ShortFlagStabilizer_mem _ _ _).mp g.property).2⟩
  invFun g := ⟨g.val.val, (generatedAxisE8ShortFlagStabilizer_mem _ _ _).mpr
    ⟨(generatedAxisE8SectionStabilizer_mem _ _).mp g.val.property, g.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full genuine Co0 outside section/short flag group has order82575360. -/
theorem generatedAxisE8Orthogonal_flag_card :
    Nat.card (generatedAxisE8ShortFlagStabilizer generatedOctadBasisOctad
      (Sum.inl (0, generatedFeasiblePhysicalRootPair))) = 82575360 := by
  rw [Nat.card_congr generatedAxisE8OrthogonalFlagEquiv,
    generatedAxisE8Orthogonal_section_point_stabilizer_card]

/-- The actual central-sign quotient of the genuine outside flag group has order41287680. -/
theorem generatedAxisE8Orthogonal_co1_flag_card :
    Nat.card (generatedAxisE8Co1ShortFlagStabilizer generatedOctadBasisOctad
      (Sum.inl (0, generatedFeasiblePhysicalRootPair))) = 41287680 := by
  let K := generatedAxisE8ShortFlagStabilizer generatedOctadBasisOctad
    (Sum.inl (0, generatedFeasiblePhysicalRootPair))
  have h := K.card_mul_index
  have hindex : K.index = 100702602000 := by
    rw [generatedAxisE8Orthogonal_flag_card, co0_card_exact] at h
    omega
  have hquotient : (generatedAxisE8Co1ShortFlagStabilizer generatedOctadBasisOctad
      (Sum.inl (0, generatedFeasiblePhysicalRootPair))).index = K.index := by
    change (K.map (QuotientGroup.mk' signsSubgroup)).index = K.index
    exact Subgroup.index_map_eq K (QuotientGroup.mk'_surjective signsSubgroup) (by
      rw [QuotientGroup.ker_mk']
      exact generatedAxisE8Short_signs_le_flagStabilizer _ _)
  have hq := (generatedAxisE8Co1ShortFlagStabilizer generatedOctadBasisOctad
    (Sum.inl (0, generatedFeasiblePhysicalRootPair))).card_mul_index
  rw [hquotient, hindex, co1_card_exact] at hq
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 100702602000)
    (hq.trans (by decide : 4157776806543360000 = 41287680 * 100702602000))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
