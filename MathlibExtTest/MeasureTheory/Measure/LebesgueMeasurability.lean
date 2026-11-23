/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.LebesgueMeasurability
public import MathlibExt.MeasureTheory.Measure.VitaliNonmeasurable
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MathlibExtTest.MeasureTheory.Measure.LebesgueMeasurability

/-- Tao's Definition 1.2.2 for Lebesgue measure on `ℝᵈ`: the instances `OuterRegular` and
`SigmaFinite` are found for `volume` on `Fin d → ℝ`. -/
example (d : ℕ) (E : Set (Fin d → ℝ)) :
    NullMeasurableSet E volume ↔
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ U, E ⊆ U ∧ IsOpen U ∧ volume (U \ E) ≤ ε :=
  nullMeasurableSet_iff_forall_exists_isOpen

/-- The same on Euclidean space `ℝᵈ` with its Euclidean structure. -/
example (d : ℕ) (E : Set (EuclideanSpace ℝ (Fin d))) :
    NullMeasurableSet E volume ↔ ∃ G, IsGδ G ∧ E ⊆ G ∧ volume (G \ E) = 0 :=
  nullMeasurableSet_iff_exists_isGδ

/-- Infinite measure is allowed: `[0, ∞)` is approximated from outside by open sets. -/
example {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, Ici (0 : ℝ) ⊆ U ∧ IsOpen U ∧ volume (U \ Ici (0 : ℝ)) ≤ ε :=
  measurableSet_Ici.nullMeasurableSet.exists_isOpen_measure_sdiff_le hε

/-- Combined with Vitali's theorem: some set of reals has no open outer approximation of
arbitrarily small error. -/
example : ∃ s : Set ℝ, ∃ ε : ℝ≥0∞, ε ≠ 0 ∧
    ∀ U, s ⊆ U → IsOpen U → ε < volume (U \ s) := by
  obtain ⟨s, hs⟩ := vitali_nonmeasurable
  rw [nullMeasurableSet_iff_forall_exists_isOpen] at hs
  push Not at hs
  obtain ⟨ε, hε, h⟩ := hs
  exact ⟨s, ε, hε, h⟩

/-- Inner approximation by closed sets for a null-measurable set of infinite measure. -/
example {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ F, F ⊆ Ioi (0 : ℝ) ∧ IsClosed F ∧ volume (Ioi (0 : ℝ) \ F) ≤ ε :=
  nullMeasurableSet_iff_forall_exists_isClosed.mp measurableSet_Ioi.nullMeasurableSet ε hε

end MathlibExtTest.MeasureTheory.Measure.LebesgueMeasurability
