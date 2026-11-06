/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8AffineData

/-! Complete signed-permutation recognition of the actual positive pointwise E8 subgroup. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

private theorem permutation_unit (p : golayAutomorphismSubgroup) (i : Fin 24) :
    (golayPermutationIsometry p).val (Pi.single i 1) = Pi.single (p.val i) 1 := by
  ext j
  change golayRealPermute p.val (Pi.single i 1) j = _
  simp only [golayRealPermute_apply, Pi.single_apply, p.val.symm_apply_eq]

private theorem pointwise_mem_monomial_of_transport (p : golayAutomorphismSubgroup)
    (g : leechIsomSubgroup) (hg : g ∈ generatedTenthE8PointwiseSpatial)
    (hi : p.val 0 ∈ generatedTenthE7OctadSupport) : g ∈ golayMonomialSubgroup := by
  let e := golayPermutationIsometry p
  let r := e⁻¹ * g * e
  have hr0 : r.val (Pi.single 0 1) = Pi.single 0 1 := by
    change e.val.symm (g.val (e.val (Pi.single 0 1))) = Pi.single 0 1
    rw [permutation_unit p 0, hg _ hi, ← permutation_unit p 0]
    exact e.val.symm_apply_apply _
  have hr : r ∈ golayMonomialSubgroup := by
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
    rw [he, map_smul, hr0]
  have he : e ∈ golayMonomialSubgroup := by
    refine ⟨0, p, ?_⟩
    have hz : golaySignIsometry 0 = 1 := golaySignHom.map_one
    rw [hz, one_mul]
  have hgr : g = e * r * e⁻¹ := by dsimp only [r]; group
  rw [hgr]
  exact golayMonomialSubgroup.mul_mem (golayMonomialSubgroup.mul_mem he hr)
    (golayMonomialSubgroup.inv_mem he)

/-- Every actual positive pointwise E8 isometry is a genuine original signed Golay permutation. -/
theorem generatedTenth_e8_pointwise_mem_monomial (g : leechIsomSubgroup)
    (hg : g ∈ generatedTenthE8PointwiseSpatial) : g ∈ golayMonomialSubgroup := by
  exact pointwise_mem_monomial_of_transport generatedTenthE8StandardPermutation g hg
    ((generatedTenth_e8_standard_permutation_support 0).mpr (by decide))

/-- The complete actual pointwise group decomposes into zero-on-E8 signs and
actual permutations fixing each of its eight coordinates. -/
theorem generatedTenth_e8_pointwise_decomposition (g : leechIsomSubgroup)
    (hg : g ∈ generatedTenthE8PointwiseSpatial) :
    ∃ c : generatedTenthE7OctadSigns, ∃ p : golayAutomorphismSubgroup,
      (∀ i ∈ generatedTenthE7OctadSupport, p.val i = i) ∧
      g = golaySignIsometry c.val * golayPermutationIsometry p := by
  obtain ⟨c, p, hcp⟩ := generatedTenth_e8_pointwise_mem_monomial g hg
  have hp (i : Fin 24) (hi : i ∈ generatedTenthE7OctadSupport) : p.val i = i := by
    have h := congrFun (hg i hi) (p.val i)
    rw [hcp] at h
    change qSign (c.val (p.val i)) *
      (Pi.single i 1 : Fin 24 → ℝ) (p.val.symm (p.val i)) =
        (Pi.single i 1 : Fin 24 → ℝ) (p.val i) at h
    rw [p.val.symm_apply_apply] at h
    by_contra hn
    simp only [Pi.single_apply, ite_true, hn, ite_false, mul_one] at h
    have hs := qSign_sq (c.val (p.val i))
    rw [h, zero_mul] at hs
    norm_num at hs
  have hc : c ∈ generatedTenthE7OctadSigns := by
    intro i hi
    have h := congrFun (hg i hi) i
    rw [hcp] at h
    change qSign (c.val i) * (Pi.single i 1 : Fin 24 → ℝ) (p.val.symm i) =
      (Pi.single i 1 : Fin 24 → ℝ) i at h
    have hpi : p.val.symm i = i := p.val.symm_apply_eq.mpr (hp i hi).symm
    simp only [hpi, Pi.single_apply, ite_true, mul_one] at h
    exact (qSign_eq_one_iff _).mp h
  exact ⟨⟨c, hc⟩, p, hp, hcp⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
