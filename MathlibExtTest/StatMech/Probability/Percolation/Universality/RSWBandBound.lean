/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.RSWBandBound

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.RSWBandBound`

* `rbb_band_crossing_lb` on the one-site box `[0, 0] × [0, 0]` (the only kind of box where its
  separation hypothesis is known to hold).
* `rbb_band_crossing_sqrt_lb` for a Dirac measure (positively associated) on the same box.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality
open StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.RSWBandBound

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

example : (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 0 0 0) :=
  rbb_band_crossing_lb 0 0 0 0 (measurableSet_horizontalCrossingEvent 0 0 0 0)
    (measurableSet_verticalCrossingEvent 0 0 0 0)
    (by rw [hCross_thin 0 0 0 le_rfl, Set.compl_univ]; exact Set.empty_subset _)
    (by rw [real_univ_eq _ (vCross_flat 0 0 0 le_rfl), real_univ_eq _ (hCross_thin 0 0 0 le_rfl)])

example (ω₀ : ConfigSpace (Sym2 (Site 2))) :
    1 - Real.sqrt (1 - 1) ≤ (Measure.dirac ω₀).real (verticalCrossingEvent 0 0 0 0) :=
  rbb_band_crossing_sqrt_lb _ (pa_dirac ω₀) (measurableSet_horizontalCrossingEvent 0 0 0 0)
    (measurableSet_verticalCrossingEvent 0 0 0 0)
    (by rw [real_univ_eq _ (vCross_flat 0 0 0 le_rfl), real_univ_eq _ (hCross_thin 0 0 0 le_rfl)])
    (by rw [real_univ_eq _ (by rw [hCross_thin 0 0 0 le_rfl, Set.univ_union])])

end MathlibExtTest.StatMech.Probability.Percolation.Universality.RSWBandBound
