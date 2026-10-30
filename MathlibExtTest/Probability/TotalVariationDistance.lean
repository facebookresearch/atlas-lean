/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TotalVariationDistance
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section

open MeasureTheory
open scoped ENNReal
open MathlibExt.Probability.TotalVariationDistance

namespace MathlibExtTest.Probability.TotalVariationDistance

/-- The total variation distance of a probability measure from itself is zero. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    totalVariationDist μ μ = 0 :=
  totalVariationDist_self

/-- Total variation distance is symmetric, restated with its exact public signature. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    totalVariationDist μ ν = totalVariationDist ν μ :=
  totalVariationDist_comm

/-- The finite-measure triangle inequality applied to probability measures. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ ν ρ : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    totalVariationDist μ ρ ≤ totalVariationDist μ ν + totalVariationDist ν ρ :=
  totalVariationDist_triangle

/-- Two Dirac measures at distinct points are at total variation distance `1`. -/
example : totalVariationDist (Measure.dirac (0 : ℝ)) (Measure.dirac 1) = 1 := by
  rw [totalVariationDist_dirac]
  norm_num

/-- Two Dirac measures at the same point are at total variation distance `0`. -/
example : totalVariationDist (Measure.dirac (0 : ℝ)) (Measure.dirac 0) = 0 := by
  rw [totalVariationDist_dirac]
  norm_num

/-- Vanishing total variation distance forces the measures to be equal:
Dirac measures at distinct points are distinct. -/
example : Measure.dirac (0 : ℝ) ≠ Measure.dirac 1 := by
  intro h
  have hTV : totalVariationDist (Measure.dirac (0 : ℝ)) (Measure.dirac 1) = 0 := by
    exact totalVariationDist_eq_zero_iff.mpr h
  rw [totalVariationDist_dirac] at hTV
  norm_num at hTV

namespace FiniteBoundary

local instance : MeasurableSpace Unit := ⊤

/-- The original unrestricted formula, retained only to reproduce the domain defect. -/
private noncomputable def legacyUnrestrictedDist (μ ν : Measure Unit) : ℝ :=
  ⨆ s : {s : Set Unit // MeasurableSet s}, |(μ s.1).toReal - (ν s.1).toReal|

private noncomputable def infiniteAtom : Measure Unit :=
  (⊤ : ℝ≥0∞) • Measure.dirac ()

private theorem infiniteAtom_ne_zero : infiniteAtom ≠ 0 := by
  intro h
  have hu := congrArg (fun μ : Measure Unit => μ Set.univ) h
  simpa [infiniteAtom, Measure.smul_apply] using hu

private theorem infiniteAtom_not_finite : ¬IsFiniteMeasure infiniteAtom := by
  intro h
  letI : IsFiniteMeasure infiniteAtom := h
  have hu := IsFiniteMeasure.measure_univ_lt_top (μ := infiniteAtom)
  simpa [infiniteAtom, Measure.smul_apply] using hu

private theorem legacy_infinite_zero_collapse : legacyUnrestrictedDist infiniteAtom 0 = 0 := by
  classical
  unfold legacyUnrestrictedDist
  have hvalues :
      (fun s : {s : Set Unit // MeasurableSet s} =>
        |(infiniteAtom s.1).toReal - ((0 : Measure Unit) s.1).toReal|) =
      fun _ => (0 : ℝ) := by
    funext s
    by_cases h : () ∈ s.1 <;>
      simp [infiniteAtom, Measure.smul_apply, Measure.dirac_apply, h]
  rw [hvalues]
  exact ciSup_const

/-- Finiteness in the new public type excludes this nonzero infinite witness. -/
example : infiniteAtom ≠ 0 ∧ ¬IsFiniteMeasure infiniteAtom ∧
    legacyUnrestrictedDist infiniteAtom 0 = 0 :=
  ⟨infiniteAtom_ne_zero, infiniteAtom_not_finite, legacy_infinite_zero_collapse⟩

private noncomputable def twiceDirac : Measure Unit :=
  Measure.dirac () + Measure.dirac ()

private instance : IsFiniteMeasure twiceDirac := by
  unfold twiceDirac
  infer_instance

private theorem twiceDirac_term_le_two (s : {s : Set Unit // MeasurableSet s}) :
    |(twiceDirac s.1).toReal - ((0 : Measure Unit) s.1).toReal| ≤ 2 := by
  classical
  by_cases h : () ∈ s.1 <;> norm_num [twiceDirac, Measure.add_apply, Measure.dirac_apply, h]

/-- The finite extension keeps the set-supremum scale for unequal total masses. -/
example : totalVariationDist twiceDirac 0 = 2 := by
  classical
  apply le_antisymm
  · change (⨆ s : {s : Set Unit // MeasurableSet s},
      |(twiceDirac s.1).toReal - ((0 : Measure Unit) s.1).toReal|) ≤ 2
    exact ciSup_le twiceDirac_term_le_two
  · have hb : BddAbove (Set.range fun s : {s : Set Unit // MeasurableSet s} =>
        |(twiceDirac s.1).toReal - ((0 : Measure Unit) s.1).toReal|) := by
      refine ⟨2, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact twiceDirac_term_le_two s
    have hu := le_ciSup hb (⟨Set.univ, MeasurableSet.univ⟩ :
      {s : Set Unit // MeasurableSet s})
    norm_num [totalVariationDist, twiceDirac, Measure.add_apply] at hu ⊢
    exact hu

/-- Non-probability finite input calls the generalized nonnegativity API. -/
example : 0 ≤ totalVariationDist twiceDirac 0 :=
  totalVariationDist_nonneg

/-- The zero measure calls the generalized diagonal API. -/
example : totalVariationDist (0 : Measure Unit) 0 = 0 :=
  totalVariationDist_self

/-- The finite symmetry API accepts unequal masses and a zero input. -/
example : totalVariationDist twiceDirac 0 = totalVariationDist 0 twiceDirac :=
  totalVariationDist_comm

/-- The finite triangle API compares masses `2`, `1` and `0`. -/
example : totalVariationDist twiceDirac 0 ≤
    totalVariationDist twiceDirac (Measure.dirac ()) +
      totalVariationDist (Measure.dirac ()) 0 :=
  totalVariationDist_triangle

/-- The finite separation API applies to a non-probability measure and zero. -/
example : totalVariationDist twiceDirac 0 = 0 ↔ twiceDirac = 0 :=
  totalVariationDist_eq_zero_iff

#print axioms infiniteAtom_ne_zero
#print axioms infiniteAtom_not_finite
#print axioms legacy_infinite_zero_collapse

end FiniteBoundary

#print axioms MathlibExt.Probability.TotalVariationDistance.totalVariationDist_nonneg
#print axioms MathlibExt.Probability.TotalVariationDistance.totalVariationDist_self
#print axioms MathlibExt.Probability.TotalVariationDistance.totalVariationDist_comm
#print axioms MathlibExt.Probability.TotalVariationDistance.totalVariationDist_triangle
#print axioms MathlibExt.Probability.TotalVariationDistance.totalVariationDist_le_one
#print axioms MathlibExt.Probability.TotalVariationDistance.totalVariationDist_eq_zero_iff
#print axioms MathlibExt.Probability.TotalVariationDistance.totalVariationDist_dirac

end MathlibExtTest.Probability.TotalVariationDistance
