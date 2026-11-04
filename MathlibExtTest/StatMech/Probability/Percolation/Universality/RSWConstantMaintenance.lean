/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.RSWConstantMaintenance

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.RSWConstantMaintenance`

* `rcm_aspect_step` for a Dirac measure (positively associated) on `[0, 1] × [0, 0]`: the band
  `[0, 1] × [0, 0]` has height zero, so its vertical crossing occurs surely and the band hypothesis
  `1/2 ≤ μ(V)` holds.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality
open StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.RSWConstantMaintenance

/-- A zero-height rectangle is crossed vertically in every configuration. -/
theorem vCross_flat (m m' c : ℤ) (h : m ≤ m') :
    verticalCrossingEvent m m' c c = Set.univ := by
  ext ω
  simp only [Set.mem_univ, iff_true]
  have hx : (![m, c] : Site 2) ∈ rect m m' c c := by simp [mem_rect, h]
  exact ⟨⟨_, hx, by simp⟩, ⟨_, hx, by simp⟩, connectedWithin_refl _ _ _⟩

/-- A zero-width rectangle is crossed horizontally in every configuration. -/
theorem hCross_thin (a c d : ℤ) (h : c ≤ d) :
    horizontalCrossingEvent a a c d = Set.univ := by
  ext ω
  simp only [Set.mem_univ, iff_true]
  have hx : (![a, c] : Site 2) ∈ rect a a c d := by simp [mem_rect, h]
  exact ⟨⟨_, hx, by simp⟩, ⟨_, hx, by simp⟩, connectedWithin_refl _ _ _⟩
/-- A Dirac measure is positively associated: a non-vacuity witness for `PositivelyAssociated`. -/
theorem pa_dirac (ω₀ : ConfigSpace (Sym2 (Site 2))) :
    PositivelyAssociated (Measure.dirac ω₀) := by
  intro A B _ _
  simp only [Measure.real, Measure.dirac_apply, Set.indicator]
  by_cases hA : ω₀ ∈ A <;> by_cases hB : ω₀ ∈ B <;> simp [hA, hB]
/-- Every probability measure gives an everywhere-occurring event probability one. -/
theorem real_univ_eq (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    {A : Set (ConfigSpace (Sym2 (Site 2)))} (h : A = Set.univ) : μ.real A = 1 := by
  rw [h, probReal_univ]

example (ω₀ : ConfigSpace (Sym2 (Site 2))) :
    0 * (1 / 2) * 0 ≤ (Measure.dirac ω₀).real (horizontalCrossingEvent 0 1 0 0) :=
  rcm_aspect_step _ (pa_dirac ω₀) (a := 0) (m := 0) (m' := 1) (b := 1) (c := 0) (d := 0)
    le_rfl zero_le_one le_rfl zero_lt_one zero_lt_one le_rfl le_rfl le_rfl
    measureReal_nonneg measureReal_nonneg
    (by rw [real_univ_eq _ (vCross_flat 0 1 0 zero_le_one)]; norm_num)

end MathlibExtTest.StatMech.Probability.Percolation.Universality.RSWConstantMaintenance
