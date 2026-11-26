/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.RSWAspectInduction

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.RSWAspectInduction`

* `rai_cross μ n 0 = 1` for every probability measure (the zero-width rectangle is crossed surely).
* Not covered: `rai_step`, `rai_cross_lb` and `rai_cross_pos` need a band-crossing bound `1/2` on
  `n × n` squares with `n > 0`; no measure in Atlas is shown both positively associated and to have
  it (a Dirac measure at the all-open configuration would, but the all-open crossings are not
  proved).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality
open StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.RSWAspectInduction

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

example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (n : ℕ) :
    rai_cross μ n 0 = 1 := by
  rw [rai_cross_def, Nat.cast_zero, zero_mul]
  exact real_univ_eq μ (hCross_thin 0 0 n (Int.natCast_nonneg n))

end MathlibExtTest.StatMech.Probability.Percolation.Universality.RSWAspectInduction
