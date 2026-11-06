/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionPointwiseTransport

/-! The full positive pointwise Co0 kernel on the actual transported E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All genuine original Co0 isometries fixing the eight actual coordinate vectors positively. -/
def generatedTenthE8PointwiseSpatial : Subgroup leechIsomSubgroup where
  carrier := {g | ∀ i ∈ generatedTenthE7OctadSupport,
    g.val (Pi.single i 1) = Pi.single i 1}
  one_mem' := by intro i _; rfl
  mul_mem' := by
    intro g h hg hh i hi
    change g.val (h.val (Pi.single i 1)) = Pi.single i 1
    rw [hh i hi, hg i hi]
  inv_mem' := by
    intro g hg i hi
    change g.val.symm (Pi.single i 1) = Pi.single i 1
    have h := congrArg g.val.symm (hg i hi)
    rw [g.val.symm_apply_apply] at h
    exact h.symm

private theorem permutation_unit (p : golayAutomorphismSubgroup) (i : Fin 24) :
    (golayPermutationIsometry p).val (Pi.single i 1) = Pi.single (p.val i) 1 := by
  ext j
  change golayRealPermute p.val (Pi.single i 1) j = _
  simp only [golayRealPermute_apply, Pi.single_apply, p.val.symm_apply_eq]

private theorem permutation_inverse_unit (p : golayAutomorphismSubgroup) (i : Fin 24) :
    (golayPermutationIsometry p).val.symm (Pi.single i 1) = Pi.single (p.val.symm i) 1 := by
  have h := congrArg (golayPermutationIsometry p).val.symm
    (permutation_unit p (p.val.symm i))
  simpa only [LinearEquiv.symm_apply_apply, Equiv.apply_symm_apply] using h.symm

/-- A genuine original Golay permutation identifies the actual transported octad
with Fifth's octad. -/
theorem generatedTenth_e8_to_original_octad :
    ∃ p : golayAutomorphismSubgroup,
      golayPermute p.val generatedTenthE7OctadWord = golayOctadWord generatedFifthFlagOctad := by
  obtain ⟨p, hp⟩ := golayOctad_to_standard generatedTenthE7OctadWord
    generatedTenth_e7_octad_mem_code generatedTenth_e7_octad_weight
  obtain ⟨q, hq⟩ := golayOctad_to_standard (golayOctadWord generatedFifthFlagOctad)
    (golayOctadWord_mem_code _) (golayOctadWord_weight _)
  refine ⟨q⁻¹ * p, ?_⟩
  change golayPermute (q.val⁻¹ * p.val) generatedTenthE7OctadWord = _
  rw [golayPermute_mul, hp, ← hq, golayPermute_inv]

/-- Conjugation by this actual positive coordinate permutation transports
the entire pointwise group. -/
def generatedTenthE8PointwiseEquiv (p : golayAutomorphismSubgroup)
    (hp : golayPermute p.val generatedTenthE7OctadWord = golayOctadWord generatedFifthFlagOctad) :
    generatedTenthE8PointwiseSpatial ≃ generatedNinthOriginalSectionPointwiseSpatial where
  toFun g := ⟨golayPermutationIsometry p * g.val * (golayPermutationIsometry p)⁻¹, by
    intro i hi
    let j := p.val.symm i
    have hw : generatedTenthE7OctadWord j = 1 := by
      change golayPermute p.val generatedTenthE7OctadWord i = 1
      rw [hp]
      exact hi
    have hj : j ∈ generatedTenthE7OctadSupport := by
      rw [generatedTenth_e7_octad_coordinates] at hw
      by_contra hn
      simp [hn] at hw
    change (golayPermutationIsometry p).val
      (g.val.val ((golayPermutationIsometry p).val.symm (Pi.single i 1))) = Pi.single i 1
    rw [permutation_inverse_unit, g.property j hj, permutation_unit]
    simp only [j, Equiv.apply_symm_apply]⟩
  invFun g := ⟨(golayPermutationIsometry p)⁻¹ * g.val * golayPermutationIsometry p, by
    intro i hi
    have hj : golayOctadWord generatedFifthFlagOctad (p.val i) = 1 := by
      rw [← hp]
      change generatedTenthE7OctadWord (p.val.symm (p.val i)) = 1
      rw [p.val.symm_apply_apply, generatedTenth_e7_octad_coordinates, ite_eq_left hi]
    change (golayPermutationIsometry p).val.symm
      (g.val.val ((golayPermutationIsometry p).val (Pi.single i 1))) = Pi.single i 1
    rw [permutation_unit, g.property _ hj, permutation_inverse_unit]
    simp only [Equiv.symm_apply_apply]⟩
  left_inv g := by
    apply Subtype.ext
    change (golayPermutationIsometry p)⁻¹ *
      (golayPermutationIsometry p * g.val * (golayPermutationIsometry p)⁻¹) *
        golayPermutationIsometry p = g.val
    group
  right_inv g := by
    apply Subtype.ext
    change golayPermutationIsometry p *
      ((golayPermutationIsometry p)⁻¹ * g.val * golayPermutationIsometry p) *
        (golayPermutationIsometry p)⁻¹ = g.val
    group

/-- The full genuine positive pointwise E8 subgroup has order 512,
including the outside permutations. -/
theorem generatedTenth_e8_pointwise_spatial_card :
    Nat.card generatedTenthE8PointwiseSpatial = 512 := by
  obtain ⟨p, hp⟩ := generatedTenth_e8_to_original_octad
  rw [Nat.card_congr (generatedTenthE8PointwiseEquiv p hp),
    generatedNinth_original_section_pointwise_spatial_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
