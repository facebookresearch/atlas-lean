/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.RSWSqrtTrick

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.RSWSqrtTrick`

* `rst_selfDual_box_crossing_half` on the one-site box `[0, 0] × [0, 0]`, where both crossings occur
  surely, so `hsep` and `hsqsym` hold. This is the only kind of box for which the separation
  hypothesis `hsep` is known to hold (it fails for `[0, 2]²`, Stage B), and the instance shows the
  lemma is not vacuous.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality
open StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.RSWSqrtTrick

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
/-- Every probability measure gives an everywhere-occurring event probability one. -/
theorem real_univ_eq (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    {A : Set (ConfigSpace (Sym2 (Site 2)))} (h : A = Set.univ) : μ.real A = 1 := by
  rw [h, probReal_univ]

example : (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent 0 0 0 0) :=
  rst_selfDual_box_crossing_half 0 0 0 0 (measurableSet_horizontalCrossingEvent 0 0 0 0)
    (measurableSet_verticalCrossingEvent 0 0 0 0)
    (by rw [hCross_thin 0 0 0 le_rfl, Set.compl_univ]; exact Set.empty_subset _)
    (by rw [real_univ_eq _ (vCross_flat 0 0 0 le_rfl), real_univ_eq _ (hCross_thin 0 0 0 le_rfl)])

end MathlibExtTest.StatMech.Probability.Percolation.Universality.RSWSqrtTrick
