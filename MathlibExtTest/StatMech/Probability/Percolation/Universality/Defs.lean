/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.Defs

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.Defs`

Tests the definitions of `StatMech.Universality`: `criticalProbability_eq_pc` at `d = 2`, the
increasing percolation event, `translateConfig` at `0` and the translated crossing events at `0`,
and the measurable-event contract of `PositivelyAssociated`, proved for the Dirac mass at the
all-open configuration (every nonempty increasing event contains it) and exercised on the
infinite configuration space `ConfigSpace ℕ`. The normalized predicate accepts a Dirac measure
scaled by `2`, while the rejected unnormalized inequality fails on `univ`. `BoxCrossingProperty`
is only restated via
`boxCrossingProperty_iff`: a witness needs crossings of all large rectangles.
-/

@[expose] public section

open MeasureTheory StatMech StatMech.Universality StatMech.Lattice StatMech.TwoDim
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.Defs

-- The real critical probability is `p_c`.
example : criticalProbability 2 = (Percolation.pc 2 : ℝ) := criticalProbability_eq_pc

example : IsIncreasing (percolationEvent 2) := percolationEvent_increasing

-- Translation by `0` is the identity.
example (ω : ConfigSpace (Sym2 (Site 2))) : translateConfig 0 ω = ω := translateConfig_zero ω

example : translatedHorizontalCrossingEvent 0 3 2 = horizontalCrossingEvent 3 2 := by simp

/-- The all-open configuration. -/
def allOpen : ConfigSpace (Sym2 (Site 2)) := fun _ => true

theorem allOpen_mem {A : Set (ConfigSpace (Sym2 (Site 2)))} (hA : IsIncreasing A)
    (hne : A.Nonempty) : allOpen ∈ A := by
  obtain ⟨a, ha⟩ := hne
  exact hA (fun _ => Bool.le_true _) ha

theorem dirac_real_of_increasing {A : Set (ConfigSpace (Sym2 (Site 2)))} (hA : IsIncreasing A)
    (hne : A.Nonempty) : (Measure.dirac allOpen).real A = 1 := by
  simp [Measure.real, Measure.dirac_apply_of_mem (allOpen_mem hA hne)]

/-- A finite scaling of the all-open Dirac measure. -/
private noncomputable def scaledDirac : Measure (ConfigSpace (Sym2 (Site 2))) :=
  (2 : NNReal) • Measure.dirac allOpen

private instance : IsFiniteMeasure scaledDirac := by
  unfold scaledDirac
  infer_instance

/-- The rejected unnormalized formulation, retained only to exhibit its scaling bug. -/
private def UnnormalizedPositiveAssociation {E : Type*}
    (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ A B : Set (ConfigSpace E), MeasurableSet A → MeasurableSet B →
    IsIncreasing A → IsIncreasing B → μ.real A * μ.real B ≤ μ.real (A ∩ B)

/-- The rejected predicate fails after scaling a Dirac probability by `2`. -/
example : ¬ UnnormalizedPositiveAssociation scaledDirac := by
  intro h
  have hu := h Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _) (fun _ _ _ _ => Set.mem_univ _)
  norm_num [UnnormalizedPositiveAssociation, scaledDirac, Measure.real,
    Measure.smul_apply] at hu

/-- Total-mass normalization makes positive association invariant under this finite scaling. -/
example : PositivelyAssociated scaledDirac := by
  intro A B hAm hBm _hA _hB
  simp only [scaledDirac, Measure.real, Measure.smul_apply,
    Measure.dirac_apply' _ hAm, Measure.dirac_apply' _ hBm,
    Measure.dirac_apply' _ (hAm.inter hBm), Measure.dirac_apply' _ MeasurableSet.univ]
  by_cases hA : allOpen ∈ A <;> by_cases hB : allOpen ∈ B <;> simp [hA, hB]

/-- On probability measures, the normalized definition is exactly the usual Harris--FKG
inequality. -/
example (μ : Measure (ConfigSpace ℕ)) [IsProbabilityMeasure μ] :
    PositivelyAssociated μ ↔
      ∀ A B : Set (ConfigSpace ℕ), MeasurableSet A → MeasurableSet B →
        IsIncreasing A → IsIncreasing B → μ.real A * μ.real B ≤ μ.real (A ∩ B) :=
  positivelyAssociated_iff_of_isProbabilityMeasure μ

-- `PositivelyAssociated` holds for the Dirac mass at the all-open configuration.
example : PositivelyAssociated (Measure.dirac allOpen) := by
  intro A B _hAm _hBm hA hB
  rcases A.eq_empty_or_nonempty with hAe | hAn
  · simp [hAe]
  rcases B.eq_empty_or_nonempty with hBe | hBn
  · simp [hBe]
  have hAB : (A ∩ B).Nonempty := ⟨allOpen, allOpen_mem hA hAn, allOpen_mem hB hBn⟩
  rw [dirac_real_of_increasing hA hAn, dirac_real_of_increasing hB hBn,
    dirac_real_of_increasing (IsUpperSet.inter hA hB) hAB]
  norm_num

/-- The event that coordinate `i` is open on the conventional infinite cube `ConfigSpace ℕ`. -/
def natOpenAt (i : ℕ) : Set (ConfigSpace ℕ) := {ω | ω i = true}

theorem measurableSet_natOpenAt (i : ℕ) : MeasurableSet (natOpenAt i) :=
  measurableSet_eq_fun (measurable_pi_apply i) measurable_const

theorem isIncreasing_natOpenAt (i : ℕ) : IsIncreasing (natOpenAt i) := by
  intro ω ω' hωω' hω
  have hi := hωω' i
  simp only [natOpenAt, Set.mem_ofPred_eq] at hω ⊢
  rw [hω] at hi
  exact top_le_iff.mp hi

-- A Harris inequality stated on measurable increasing events constructs positive association.
example (μ : Measure (ConfigSpace ℕ)) [IsProbabilityMeasure μ]
    (hHarris : ∀ A B : Set (ConfigSpace ℕ), MeasurableSet A → MeasurableSet B →
      IsIncreasing A → IsIncreasing B → μ.real A * μ.real B ≤ μ.real (A ∩ B)) :
    PositivelyAssociated μ :=
  (positivelyAssociated_iff_of_isProbabilityMeasure μ).mpr hHarris

-- The measurable-event API is consumed on an infinite (not finite-vacuous) configuration space.
example (μ : Measure (ConfigSpace ℕ)) [IsFiniteMeasure μ] (hpa : PositivelyAssociated μ) :
    μ.real (natOpenAt 0) * μ.real (natOpenAt 0) ≤
      μ.real (natOpenAt 0) * μ.real Set.univ :=
  hpa.sq_le_self (natOpenAt 0) (measurableSet_natOpenAt 0) (isIncreasing_natOpenAt 0)

-- `BoxCrossingProperty` unfolds to a positive infimum of crossing probabilities.
example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) :
    BoxCrossingProperty μ 2 ↔ 1 < (2 : ℝ) ∧ ∃ n0 : ℕ, 0 < sInf (boxCrossingProbabilities μ 2 n0) :=
  boxCrossingProperty_iff μ 2

end MathlibExtTest.StatMech.Probability.Percolation.Universality.Defs
