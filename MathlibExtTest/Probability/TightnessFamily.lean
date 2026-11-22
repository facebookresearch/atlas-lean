/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TightnessFamily
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

open MeasureTheory
open scoped ENNReal
open MathlibExt.Probability.TightnessFamily

namespace MathlibExtTest.Probability.TightnessFamily

/-- A constant family of Dirac measures is tight in the compact-set form. -/
example : IsTightFamily (fun _ : ℕ => Measure.dirac (0 : ℝ)) :=
  isTightFamily_of_singleton

/-- A constant family of Dirac measures is tight in the interval form. -/
example : IsTightFamilyReal (fun _ : ℕ => Measure.dirac (0 : ℝ)) :=
  isTightFamily_of_singleton.isTightFamilyReal

/-- The Dirac-at-`n` family is not tight: its mass escapes every bounded
interval. -/
example : ¬ IsTightFamilyReal (fun n : ℕ => Measure.dirac (n : ℝ)) := by
  intro h
  obtain ⟨M, hM⟩ := h (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have hnot : (n : ℝ) ∉ Set.Icc (-M) M := by
    intro hmem
    exact (not_le.mpr hn) hmem.2
  have h0 : Measure.dirac (n : ℝ) (Set.Icc (-M) M) = 0 :=
    (dirac_eq_zero_iff_not_mem measurableSet_Icc).mpr hnot
  have hle : (1 : ℝ≥0∞) - 1 / 2 ≤ 0 := by simpa [h0] using hM n
  rw [tsub_le_iff_right] at hle
  simp only [zero_add] at hle
  norm_num at hle


/-- The generic public API identifies the very same canonical set of measures. -/
theorem family_tightness_iff_canonical {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] {ι : Type*} {μ : ι → Measure α}
    [∀ i, IsProbabilityMeasure (μ i)] :
    IsTightFamily μ ↔ IsTightMeasureSet (Set.range μ) :=
  isTightFamily_iff_isTightMeasureSet

section NonmeasurableCompacts

local instance : TopologicalSpace ℕ := ⊥
local instance : MeasurableSpace ℕ := ⊥

private theorem coarseProbability_nonempty (s : Set ℕ) (hs : s.Nonempty) :
    (@Measure.dirac ℕ ⊥ 0) s = 1 := by
  have ht : toMeasurable (@Measure.dirac ℕ ⊥ 0) s = Set.univ := by
    rcases MeasurableSpace.measurableSet_bot_iff.mp
        (measurableSet_toMeasurable (@Measure.dirac ℕ ⊥ 0) s) with he | hu
    · obtain ⟨n, hn⟩ := hs
      have hn' : n ∈ (∅ : Set ℕ) := he ▸ subset_toMeasurable (@Measure.dirac ℕ ⊥ 0) s hn
      exact False.elim hn'
    · exact hu
  rw [← measure_toMeasurable (μ := (@Measure.dirac ℕ ⊥ 0)) s, ht, measure_univ]

/-- The compact singleton in the regression fixture is not measurable. -/
theorem compact_singleton_not_measurable :
    ¬ @MeasurableSet ℕ ⊥ ({0} : Set ℕ) := by
  intro h
  rcases MeasurableSpace.measurableSet_bot_iff.mp h with he | hu
  · have h0 : (0 : ℕ) ∈ (∅ : Set ℕ) := he ▸ (by simp : (0 : ℕ) ∈ ({0} : Set ℕ))
    exact h0
  · have h1 : (1 : ℕ) ∈ ({0} : Set ℕ) := hu.symm ▸ (by trivial)
    exact (by decide : (1 : ℕ) ∉ ({0} : Set ℕ)) h1

/-- A nonmeasurable compact singleton satisfies the removed mass predicate. -/
theorem nonmeasurable_compact_mass_witness :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set ℕ, IsCompact K ∧
      ∀ _ : Unit, (@Measure.dirac ℕ ⊥ 0) K ≥ 1 - ε := by
  intro ε _
  refine ⟨{0}, isCompact_singleton, fun _ => ?_⟩
  change (1 : ℝ≥0∞) - ε ≤ Measure.dirac (0 : ℕ) ({0} : Set ℕ)
  rw [Measure.dirac_apply_of_mem (a := (0 : ℕ)) (s := ({0} : Set ℕ)) (by simp)]
  exact tsub_le_self

/-- Canonical family tightness rejects the same coarse-space probability measure. -/
theorem nonmeasurable_compact_family_not_tight :
    ¬ IsTightFamily (fun _ : Unit => (@Measure.dirac ℕ ⊥ 0)) := by
  intro h
  rw [IsTightFamily, isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at h
  obtain ⟨K, hK, hMass⟩ := h (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := (isCompact_iff_finite.mp hK).exists_notMem
  have hcompl := coarseProbability_nonempty Kᶜ ⟨n, hn⟩
  have hle := hMass (@Measure.dirac ℕ ⊥ 0) ⟨(), rfl⟩
  rw [hcompl] at hle
  norm_num at hle

end NonmeasurableCompacts

end MathlibExtTest.Probability.TightnessFamily
