/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitGroup

/-! Every actual original matrix fixer preserves the entire actual standard E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem real_section_transport (x : Fin 24 → ℝ) :
    (golayPermutationIsometry generatedTenthE8StandardPermutation).val x ∈
      generatedTenthE8CoordinateSection ↔ ∀ i : Fin 24, 8 ≤ i.val → x i = 0 := by
  constructor
  · intro h i hi
    have hn : generatedTenthE8StandardPermutation.val i ∉ generatedTenthE7OctadSupport := by
      rw [generatedTenth_e8_standard_permutation_support]
      omega
    have hv := h (generatedTenthE8StandardPermutation.val i) hn
    change x (generatedTenthE8StandardPermutation.val.symm
      (generatedTenthE8StandardPermutation.val i)) = 0 at hv
    rw [generatedTenthE8StandardPermutation.val.symm_apply_apply] at hv
    exact hv
  · intro h i hi
    change x (generatedTenthE8StandardPermutation.val.symm i) = 0
    apply h
    have hs := generatedTenth_e8_standard_permutation_support
      (generatedTenthE8StandardPermutation.val.symm i)
    rw [generatedTenthE8StandardPermutation.val.apply_symm_apply] at hs
    exact Nat.le_of_not_gt (fun hlt => hi (hs.mpr hlt))

/-- Genuine source permutation identifies the whole actual integral standard E8 section. -/
theorem generatedTenth_e7_root_orbit_e8_transport (u : leechIntegral) :
    (golayPermutationIsometry generatedTenthE8StandardPermutation).val
      (leechCoordinateEmbedding u.val) ∈ generatedTenthE8CoordinateSection ↔
        u ∈ generatedTenthE7StandardE8Section := by
  rw [real_section_transport, generatedTenth_e7_standard_e8_section_mem]
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  change (∀ i : Fin 24, 8 ≤ i.val → (u.val i : ℝ) / Real.sqrt 8 = 0) ↔ _
  simp only [div_eq_zero_iff, hsqrt, or_false, Int.cast_eq_zero]

/-- Every actual whole matrix-group member preserves the complete standard integral E8 section. -/
theorem generatedTenth_e7_root_orbit_e8_section
    (g : generatedTenthE7StandardMatrixGroup) (u : leechIntegral) :
    u ∈ generatedTenthE7StandardE8Section ↔
      leechIntegralAction g.val u ∈ generatedTenthE7StandardE8Section := by
  let p := golayPermutationIsometry generatedTenthE8StandardPermutation
  have ht : generatedTenthE7TransportedSpatial (generatedTenthE7OrbitConjugation g.val) =
      p * g.val * p⁻¹ := by
    simp [p, generatedTenthE7TransportedSpatial, generatedTenthE7OrbitConjugation,
      generatedTenthE7OrbitTransport, mul_assoc]
  have h := generatedTenth_e7_matrix_fixer_e8_section
    (generatedTenthE7OrbitConjugation g.val) g.property (p.val (leechCoordinateEmbedding u.val))
  rw [ht] at h
  have he : (p * g.val * p⁻¹).val (p.val (leechCoordinateEmbedding u.val)) =
      p.val (leechCoordinateEmbedding (leechIntegralAction g.val u).val) := by
    change p.val (g.val.val (p.val.symm (p.val (leechCoordinateEmbedding u.val)))) = _
    rw [LinearEquiv.symm_apply_apply, leechIntegralAction_embedding]
  rw [he] at h
  exact (generatedTenth_e7_root_orbit_e8_transport u).symm.trans
    (h.trans (generatedTenth_e7_root_orbit_e8_transport (leechIntegralAction g.val u)))

/-- The whole actual section maps onto itself, with no generated-subgroup assumption. -/
theorem generatedTenth_e7_root_orbit_e8_section_map
    (g : generatedTenthE7StandardMatrixGroup) :
    generatedTenthE7StandardE8Section.map (leechIntegralAction g.val).toLinearMap =
      generatedTenthE7StandardE8Section := by
  apply Submodule.ext
  intro u
  rw [Submodule.mem_map_equiv]
  have h := generatedTenth_e7_root_orbit_e8_section g ((leechIntegralAction g.val).symm u)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
