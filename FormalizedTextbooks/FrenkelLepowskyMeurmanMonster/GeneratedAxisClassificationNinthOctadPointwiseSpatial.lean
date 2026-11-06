/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadMonomialSubgroup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechConcreteGeneration

/-! The entire actual lattice-isometry pointwise octad fixer is the counted monomial group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual lattice isometries fixing every positive coordinate vector of the recovered octad. -/
def generatedNinthOctadPointwiseSpatial : Subgroup leechIsomSubgroup where
  carrier := {g | ∀ i : Fin 24,
    (golayEncodedMask generatedNinthSectionCode.val).testBit i.val = true →
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

private theorem generatedNinthOctadRealPermutation_single (p : Equiv.Perm (Fin 24))
    (i : Fin 24) : golayRealPermute p (Pi.single i 1 : Fin 24 → ℝ) = Pi.single (p i) 1 := by
  ext j
  have h : p.symm j = i ↔ j = p i := p.symm_apply_eq
  simp only [golayRealPermute_apply, Pi.single_apply, h]

/-- Every counted actual sign/permutation pair fixes the specified positive coordinate vectors. -/
theorem generatedNinth_octad_monomial_le_pointwise :
    generatedNinthOctadMonomialSubgroup ≤ generatedNinthOctadPointwiseSpatial := by
  rintro g ⟨c, p, rfl⟩ i hi
  change golayRealSign c.val.val (golayRealPermute p.val.val (Pi.single i 1)) = Pi.single i 1
  rw [generatedNinthOctadRealPermutation_single, p.property i hi]
  ext j
  by_cases hj : j = i
  · subst j
    simp only [golayRealSign_apply, Pi.single_apply, ite_true, c.property i hi,
      qSign_zero, mul_one]
  · simp only [golayRealSign_apply, Pi.single_apply, hj, ite_false, mul_zero]

/-- Every actual lattice isometry fixing the positive octad already belongs
to the monomial group. -/
theorem generatedNinth_octad_pointwise_le_monomial :
    generatedNinthOctadPointwiseSpatial ≤ generatedNinthOctadMonomialSubgroup := by
  intro g hg
  have h0 : (golayEncodedMask generatedNinthSectionCode.val).testBit 0 = true := by
    decide +kernel
  have hmono : g ∈ golayMonomialSubgroup := by
    apply leech_fix_frame_mem_monomial
    apply Subtype.ext
    apply leechCoordinateEmbedding_injective
    rw [leechIntegralAction_embedding]
    have he : leechCoordinateEmbedding (leechCoordinateFrameLattice 0).val =
        (8 / Real.sqrt 8 : ℝ) • (Pi.single 0 1 : Fin 24 → ℝ) := by
      ext j
      by_cases hj : j = 0 <;>
        simp [leechCoordinateEmbedding, leechCoordinateFrameLattice,
          leechCoordinateFrameVector, hj]
    rw [he, map_smul, hg 0 h0]
  obtain ⟨c, p, hcp⟩ := hmono
  have hfix (i : Fin 24) (hi :
      (golayEncodedMask generatedNinthSectionCode.val).testBit i.val = true) : p.val i = i := by
    have h := congrFun (hg i hi) (p.val i)
    rw [hcp] at h
    change qSign (c.val (p.val i)) * (Pi.single i 1 : Fin 24 → ℝ) (p.val.symm (p.val i)) =
      (Pi.single i 1 : Fin 24 → ℝ) (p.val i) at h
    rw [p.val.symm_apply_apply] at h
    by_contra hn
    simp only [Pi.single_apply, ite_true, hn, ite_false, mul_one] at h
    have hs := qSign_sq (c.val (p.val i))
    rw [h, zero_mul] at hs
    norm_num at hs
  have hc : c ∈ generatedNinthOctadSignSpace generatedNinthSectionCode := by
    intro i hi
    have h := congrFun (hg i hi) i
    rw [hcp] at h
    change qSign (c.val i) * (Pi.single i 1 : Fin 24 → ℝ) (p.val.symm i) =
      (Pi.single i 1 : Fin 24 → ℝ) i at h
    have hpi : p.val.symm i = i := p.val.symm_apply_eq.mpr (hfix i hi).symm
    simp only [hpi, Pi.single_apply, ite_true, mul_one] at h
    exact (qSign_eq_one_iff _).mp h
  exact ⟨⟨c, hc⟩, ⟨p, hfix⟩, hcp⟩

/-- The complete positive pointwise octad fixer is exactly the counted genuine monomial subgroup. -/
theorem generatedNinth_octad_pointwise_spatial_eq :
    generatedNinthOctadPointwiseSpatial = generatedNinthOctadMonomialSubgroup :=
  le_antisymm generatedNinth_octad_pointwise_le_monomial
    generatedNinth_octad_monomial_le_pointwise

/-- Exactly 512 actual lattice isometries fix the recovered octad pointwise with positive signs. -/
theorem generatedNinth_octad_pointwise_spatial_card :
    Nat.card generatedNinthOctadPointwiseSpatial = 512 := by
  rw [generatedNinth_octad_pointwise_spatial_eq, generatedNinthOctadMonomialSubgroup_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
