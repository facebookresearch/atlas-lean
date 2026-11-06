/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionBinarySigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionSpan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechConcreteGeneration

/-! The uniform root sign is the uniform physical sign on every selected octad coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A common actual root scalar acts with that scalar on the whole supported lattice span. -/
theorem generatedNinth_section_scalar_supported (g : leechIsomSubgroup) (c : ℝ)
    (hroot : ∀ j : Fin 8,
      g.val (generatedNinthSectionRealRoot j) = c • generatedNinthSectionRealRoot j)
    (u : leechIntegral)
    (hu : generatedOctadSupported (golayOctadWord generatedFifthFlagOctad) u.val) :
    g.val (leechCoordinateEmbedding u.val) = c • leechCoordinateEmbedding u.val := by
  obtain ⟨a, ha⟩ := generatedFifthFrame_integer_span u hu
  have he := congrArg (fun v : leechIntegral => leechCoordinateEmbedding v.val) ha
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul] at he
  change leechCoordinateEmbedding u.val =
    ∑ j : Fin 8, a j • generatedNinthSectionRealRoot j at he
  rw [he, map_sum]
  simp_rw [map_zsmul, hroot]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm (a j) c (generatedNinthSectionRealRoot j)

/-- The supported coordinate-frame lattice vector has its actual nonzero physical scale. -/
theorem generatedNinth_section_coordinate_frame_embedding (i : Fin 24) :
    leechCoordinateEmbedding (leechCoordinateFrameLattice i).val =
      (8 / Real.sqrt 8 : ℝ) • (Pi.single i 1 : Fin 24 → ℝ) := by
  ext j
  by_cases hj : j = i <;>
    simp [leechCoordinateEmbedding, leechCoordinateFrameLattice,
      leechCoordinateFrameVector, hj]

/-- A common root scalar fixes each supported positive physical coordinate with that scalar. -/
theorem generatedNinth_section_scalar_coordinate (g : leechIsomSubgroup) (c : ℝ)
    (hroot : ∀ j : Fin 8,
      g.val (generatedNinthSectionRealRoot j) = c • generatedNinthSectionRealRoot j)
    (i : Fin 24) (hi : golayOctadWord generatedFifthFlagOctad i = 1) :
    g.val (Pi.single i 1) = c • (Pi.single i 1 : Fin 24 → ℝ) := by
  have hu : generatedOctadSupported (golayOctadWord generatedFifthFlagOctad)
      (leechCoordinateFrameLattice i).val := by
    intro j hj
    by_cases hji : j = i
    · subst j
      rw [hi] at hj
      exact (one_ne_zero hj).elim
    · simp only [leechCoordinateFrameLattice, leechCoordinateFrameVector,
        Pi.single_apply, hji, ite_false]
  have hg := generatedNinth_section_scalar_supported g c hroot
    (leechCoordinateFrameLattice i) hu
  rw [generatedNinth_section_coordinate_frame_embedding, map_smul] at hg
  have hc : (8 / Real.sqrt 8 : ℝ) ≠ 0 := by positivity
  ext j
  have he := congrFun hg j
  have hm : (8 / Real.sqrt 8 : ℝ) * g.val (Pi.single i 1) j =
      (8 / Real.sqrt 8 : ℝ) * (c * (Pi.single i 1 : Fin 24 → ℝ) j) := by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm] using he
  exact mul_left_cancel₀ hc hm

/-- Actual binary fixation forces a uniform positive or negative action on the selected octad. -/
theorem generatedNinth_section_binary_uniform_coordinate_sign (g : leechIsomSubgroup)
    (hfix : ∀ j : Fin 8,
      leechModTwoAction g (leechReduction (generatedFifthFrameRoot j)) =
        leechReduction (generatedFifthFrameRoot j)) :
    (∀ i : Fin 24, golayOctadWord generatedFifthFlagOctad i = 1 →
      g.val (Pi.single i 1) = Pi.single i 1) ∨
    (∀ i : Fin 24, golayOctadWord generatedFifthFlagOctad i = 1 →
      g.val (Pi.single i 1) = -(Pi.single i 1 : Fin 24 → ℝ)) := by
  rcases generatedNinth_section_binary_uniform_root_sign g hfix with hp | hn
  · left
    intro i hi
    have hs : ∀ j : Fin 8, g.val (generatedNinthSectionRealRoot j) =
        (1 : ℝ) • generatedNinthSectionRealRoot j := by
      simpa only [one_smul] using hp
    simpa only [one_smul] using generatedNinth_section_scalar_coordinate g 1 hs i hi
  · right
    intro i hi
    have hs : ∀ j : Fin 8, g.val (generatedNinthSectionRealRoot j) =
        (-1 : ℝ) • generatedNinthSectionRealRoot j := by
      simpa only [neg_one_smul] using hn
    simpa only [neg_one_smul] using generatedNinth_section_scalar_coordinate g (-1) hs i hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
