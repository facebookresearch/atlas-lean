/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8PointwiseCount

/-! Positive pointwise coordinate fixation is exactly fixation of the entire actual E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every real coordinate vector is its complete coordinate-basis sum. -/
private theorem coordinate_sum (x : Fin 24 → ℝ) :
    x = ∑ i : Fin 24, x i • Pi.single i (1 : ℝ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]

/-- The actual positive coordinate pointwise group fixes every vector in the full E8 section. -/
theorem generatedTenth_e8_pointwise_fixes_section (g : generatedTenthE8PointwiseSpatial)
    (x : Fin 24 → ℝ) (hx : x ∈ generatedTenthE8CoordinateSection) : g.val.val x = x := by
  rw [coordinate_sum x, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ generatedTenthE7OctadSupport
  · rw [map_smul, g.property i hi]
  · have hz : x i = 0 := hx i hi
    simp [hz]

/-- Membership in the counted 512 group means exactly whole-section positive fixation. -/
theorem generatedTenth_e8_pointwise_mem_iff (g : leechIsomSubgroup) :
    g ∈ generatedTenthE8PointwiseSpatial ↔
      ∀ x ∈ generatedTenthE8CoordinateSection, g.val x = x := by
  constructor
  · intro hg x hx
    exact generatedTenth_e8_pointwise_fixes_section ⟨g, hg⟩ x hx
  · intro h i hi
    apply h
    intro j hj
    have hji : j ≠ i := by
      intro heq
      exact hj (heq ▸ hi)
    simp [Pi.single_apply, hji, Ne.symm hji]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
