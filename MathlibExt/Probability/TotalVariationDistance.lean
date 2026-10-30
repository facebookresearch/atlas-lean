/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

section

open MeasureTheory

namespace MathlibExt.Probability.TotalVariationDistance

/-!
# Supremum total variation distance between finite measures

For finite measures `μ` and `ν` on the same measurable space, define the
supremum of `|μ(B) - ν(B)|` over measurable sets `B`. Finiteness makes
conversion of the masses to real numbers valid. The core metric properties
proved here hold for finite measures: nonnegativity, separation,
symmetry and the triangle inequality. The bound `1` is specific to
probability measures. The Dirac computations use probability laws.

## Source

The target “Definition (total variation distance)” in
`v1/Atlas/TheoryOfProbability/targets.yaml` (Lecture 12) defines this for
two probability measures. Its archived definition in
`v1/Atlas/TheoryOfProbability/code/TotalVariation.lean` omitted that
restriction. This API corrects the omission by requiring finite measures
explicitly; its probability specialization matches the source supremum.
The subtype of measurable sets replaces the archive's double `iSup`.
The finite-measure metric-property proofs are new extensions of the
probability-measure source definition.

Mathlib's `SignedMeasure.totalVariation` is a measure-valued operation
on a signed measure. The function here uses the source's set-supremum
convention; no identification with a signed-measure norm or a density
integral is used. Existing probability-measure topology/metric instances
are unaffected by this namespace of functions and propositions.

## Main results

* `totalVariationDist`: `‖μ - ν‖ = sup_B |μ(B) - ν(B)|`.
* `totalVariationDist_nonneg`, `totalVariationDist_self`,
  `totalVariationDist_comm`, `totalVariationDist_triangle`,
  `totalVariationDist_le_one`: the finite-measure metric axioms, with
  the bound `≤ 1` for probability measures.
* `totalVariationDist_eq_zero_iff`: the distance vanishes iff the
  measures are equal.
* `totalVariationDist_dirac`: the distance between `δ a` and `δ b`
  is `0` if `a = b` and `1` otherwise.
-/

/-- The supremum distance between finite measures, using real masses.
The probability-measure specialization is the Lecture 12 definition.
The inline finiteness binders are part of this public interface. -/
noncomputable def totalVariationDist {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  ⨆ s : {s : Set Ω // MeasurableSet s}, |(μ s.1).toReal - (ν s.1).toReal|

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν ρ : Measure Ω}

/-- Each term in the total variation supremum is at most `1`, for
probability measures: both masses lie in `[0, 1]`. -/
private lemma abs_toReal_sub_le_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Ω} : |(μ s).toReal - (ν s).toReal| ≤ 1 := by
  have hμ0 : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
  have hμ1 : (μ s).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono (measure_ne_top μ Set.univ)
      (measure_mono (Set.subset_univ s))
    rwa [measure_univ, ENNReal.toReal_one] at h
  have hν0 : 0 ≤ (ν s).toReal := ENNReal.toReal_nonneg
  have hν1 : (ν s).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono (measure_ne_top ν Set.univ)
      (measure_mono (Set.subset_univ s))
    rwa [measure_univ, ENNReal.toReal_one] at h
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- Every measurable-set contribution is bounded by the sum of the two real total masses. -/
private lemma abs_toReal_sub_le_total_mass [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set Ω} :
    |(μ s).toReal - (ν s).toReal| ≤ (μ Set.univ).toReal + (ν Set.univ).toReal := by
  have hμ0 : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
  have hν0 : 0 ≤ (ν s).toReal := ENNReal.toReal_nonneg
  have hμ : (μ s).toReal ≤ (μ Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ s))
  have hν : (ν s).toReal ≤ (ν Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top ν Set.univ) (measure_mono (Set.subset_univ s))
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- Finite total masses bound the family defining the distance. -/
private lemma bddAbove_range [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    BddAbove (Set.range fun s : {s : Set Ω // MeasurableSet s} =>
      |(μ s.1).toReal - (ν s.1).toReal|) := by
  refine ⟨(μ Set.univ).toReal + (ν Set.univ).toReal, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact abs_toReal_sub_le_total_mass

/-- A single measurable set contributes at most the total variation
distance. -/
private lemma le_totalVariationDist [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) :
    |(μ s).toReal - (ν s).toReal| ≤ totalVariationDist μ ν :=
  le_ciSup bddAbove_range ⟨s, hs⟩

/-- The subtype of measurable sets is nonempty (it contains `univ`). -/
instance : Nonempty {s : Set Ω // MeasurableSet s} :=
  ⟨⟨Set.univ, MeasurableSet.univ⟩⟩

/-- To bound the total variation distance it suffices to bound every
measurable set's contribution. -/
private lemma totalVariationDist_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : ℝ} (h : ∀ s : Set Ω, MeasurableSet s →
      |(μ s).toReal - (ν s).toReal| ≤ C) :
    totalVariationDist μ ν ≤ C :=
  ciSup_le fun s => h s.1 s.2

/-- Total variation distance is nonnegative. -/
theorem totalVariationDist_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ totalVariationDist μ ν := by
  have h := le_totalVariationDist (μ := μ) (ν := ν) MeasurableSet.empty
  simpa using h

/-- The total variation distance of a finite measure from itself is zero. -/
theorem totalVariationDist_self [IsFiniteMeasure μ] :
    totalVariationDist μ μ = 0 := by
  refine le_antisymm ?_ totalVariationDist_nonneg
  refine totalVariationDist_le fun s _ => ?_
  simp

/-- The supremum distance is symmetric for finite measures. -/
theorem totalVariationDist_comm [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    totalVariationDist μ ν = totalVariationDist ν μ := by
  show (⨆ s : {s : Set Ω // MeasurableSet s}, |(μ s.1).toReal - (ν s.1).toReal|) =
    ⨆ s : {s : Set Ω // MeasurableSet s}, |(ν s.1).toReal - (μ s.1).toReal|
  exact iSup_congr fun s => abs_sub_comm _ _

/-- Total variation distance satisfies the triangle inequality for finite measures. -/
theorem totalVariationDist_triangle [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] :
    totalVariationDist μ ρ ≤ totalVariationDist μ ν + totalVariationDist ν ρ := by
  refine totalVariationDist_le fun s hs => ?_
  calc |(μ s).toReal - (ρ s).toReal|
      = |((μ s).toReal - (ν s).toReal) + ((ν s).toReal - (ρ s).toReal)| := by
        congr 1
        ring
    _ ≤ |(μ s).toReal - (ν s).toReal| + |(ν s).toReal - (ρ s).toReal| :=
        abs_add_le _ _
    _ ≤ totalVariationDist μ ν + totalVariationDist ν ρ :=
        add_le_add (le_totalVariationDist hs) (le_totalVariationDist hs)

/-- Total variation distance between probability measures is at most `1`. -/
theorem totalVariationDist_le_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariationDist μ ν ≤ 1 :=
  totalVariationDist_le fun _ _ => abs_toReal_sub_le_one

/-- Total variation distance vanishes iff the finite measures are equal. -/
theorem totalVariationDist_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    totalVariationDist μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    apply Measure.ext
    intro s hs
    have hle : |(μ s).toReal - (ν s).toReal| ≤ 0 := by
      calc |(μ s).toReal - (ν s).toReal| ≤ totalVariationDist μ ν :=
            le_totalVariationDist hs
        _ = 0 := h
    have hterm : |(μ s).toReal - (ν s).toReal| = 0 :=
      le_antisymm hle (abs_nonneg _)
    have hEq : (μ s).toReal = (ν s).toReal := by
      have hsub : (μ s).toReal - (ν s).toReal = 0 := abs_eq_zero.mp hterm
      exact sub_eq_zero.mp hsub
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ s)
      (measure_ne_top ν s)).mp hEq
  · intro h
    subst μ
    exact totalVariationDist_self

/-- The total variation distance between two Dirac measures is `0` if
they are at the same point and `1` otherwise. -/
theorem totalVariationDist_dirac [MeasurableSingletonClass Ω] [DecidableEq Ω] {a b : Ω} :
    totalVariationDist (Measure.dirac a) (Measure.dirac b) =
      if a = b then 0 else 1 := by
  by_cases hab : a = b
  · subst hab
    simp [totalVariationDist_self]
  · rw [ite_eq_right hab]
    refine le_antisymm totalVariationDist_le_one ?_
    have h := le_totalVariationDist (μ := Measure.dirac a) (ν := Measure.dirac b)
      (MeasurableSet.singleton a)
    have hda : Measure.dirac a {a} = 1 :=
      Measure.dirac_apply_of_mem (Set.mem_singleton a)
    have hdb : Measure.dirac b {a} = 0 := by
      rw [Measure.dirac_apply]
      refine Set.indicator_of_notMem ?_ 1
      simp only [Set.mem_singleton_iff]
      exact fun hEq => hab hEq.symm
    rw [hda, hdb] at h
    simpa using h

end MathlibExt.Probability.TotalVariationDistance

end
