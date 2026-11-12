/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianCdf
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Real
public import MathlibExt.Probability.CdfContinuityPoints

/-!
# Tests for continuity of the Gaussian cdf

Standard use at the standard normal, the degenerate zero-variance Gaussian
(a Dirac mass by `gaussianReal_zero_var`) showing the nonzero-variance
hypothesis cannot be dropped, and the singleton-null round trip through the
continuity iff.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.GaussianCdf

/-- Use: the standard normal cdf is continuous. -/
example : Continuous (cdf (gaussianReal 0 1)) := by
  exact continuous_cdf_gaussianReal 0 one_ne_zero

/-- Boundary: the zero-variance Gaussian cdf is not continuous, so `hv` cannot be dropped. -/
example : ¬ Continuous (cdf (gaussianReal 0 0)) := by
  rw [gaussianReal_zero_var]
  intro h
  have h0 : ContinuousAt (cdf (Measure.dirac (0 : ℝ))) 0 := h.continuousAt
  rw [MathlibExt.Probability.CdfContinuityPoints.continuousAt_cdf_iff_measure_singleton_eq_zero] at h0
  have h1 : Measure.dirac (0 : ℝ) {(0 : ℝ)} = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_singleton _)
  rw [h1] at h0
  exact one_ne_zero h0

/-- Use: a Gaussian with nonzero variance has no atoms (round trip through the iff). -/
example (μ : ℝ) {v : NNReal} (hv : v ≠ 0) (x : ℝ) :
    (gaussianReal μ v) {x} = 0 := by
  have h := continuous_cdf_gaussianReal μ hv
  have hx : ContinuousAt (cdf (gaussianReal μ v)) x := h.continuousAt
  rw [MathlibExt.Probability.CdfContinuityPoints.continuousAt_cdf_iff_measure_singleton_eq_zero] at hx
  exact hx


/-- Use: at `μ = 0`, `v = 1` the identity is definitional up to the coercions. -/
example (x : ℝ) :
    cdf (gaussianReal 0 1) x
      = cdf (gaussianReal 0 1) ((x - 0) / Real.sqrt ((1 : NNReal) : ℝ)) := by
  have h : (x - 0) / Real.sqrt ((1 : NNReal) : ℝ) = x := by simp
  rw [h]

/-- Use: at `x = μ` the cdf equals the standard normal cdf at `0`. -/
example (μ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    cdf (gaussianReal μ v) μ = cdf (gaussianReal 0 1) 0 := by
  have h := cdf_gaussianReal_eq_std μ μ hv
  have h0 : (μ - μ) / Real.sqrt (v:ℝ) = 0 := by simp
  rwa [h0] at h

/-- Boundary: the identity is false at `v = 0` (`hv` is necessary). -/
example :
    cdf (gaussianReal 0 0) 0
      ≠ cdf (gaussianReal 0 1) ((0 - 0) / Real.sqrt ((0 : NNReal) : ℝ)) := by
  rw [gaussianReal_zero_var]
  have harg : (0 - 0 : ℝ) / Real.sqrt ((0 : NNReal) : ℝ) = 0 := by simp
  rw [harg]
  have hmem : (0:ℝ) ∈ Set.Iic 0 := Set.mem_Iic.mpr le_rfl
  have hL : cdf (Measure.dirac 0) 0 = 1 := by
    rw [cdf_eq_real, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic,
      Set.indicator_of_mem hmem]
    simp
  rw [hL]
  have hneg : Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0:ℝ)) (v := (1:NNReal))
  have hnull : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  have hsing0 : (gaussianReal 0 1) {0} = 0 := @measure_singleton _ _ _ hnull 0
  have hsing : (gaussianReal 0 1).real {0} = 0 := by
    rw [measureReal_def, hsing0]
    simp
  have hpre : (fun x : ℝ => -x) ⁻¹' (Set.Iic 0) = Set.Ici 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
    constructor <;> intro h <;> linarith
  have hIci : (gaussianReal 0 1).real (Set.Iic 0)
      = (gaussianReal 0 1).real (Set.Ici 0) := by
    have h := map_measureReal_apply (μ := gaussianReal 0 1) (f := fun x : ℝ => -x)
      (s := Set.Iic 0) measurable_neg measurableSet_Iic
    rw [hneg, hpre] at h
    exact h
  have hunion : Set.Ioi (0:ℝ) ∪ {0} = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff, Set.mem_Ici]
    constructor
    · rintro (h | rfl)
      · exact le_of_lt h
      · exact le_rfl
    · intro h
      by_cases h' : (0:ℝ) < x
      · exact Or.inl h'
      · exact Or.inr (le_antisymm (not_lt.mp h') h)
  have hdisj : Disjoint (Set.Ioi (0:ℝ)) {0} := by
    rw [Set.disjoint_left]
    intro x hx h
    rw [Set.mem_singleton_iff] at h
    rw [Set.mem_Ioi] at hx
    linarith
  have hIoi : (gaussianReal 0 1).real (Set.Ioi 0)
      = (gaussianReal 0 1).real (Set.Iic 0) := by
    have h := measureReal_union (μ := gaussianReal 0 1) (s₁ := Set.Ioi 0) (s₂ := ({0} : Set ℝ))
      hdisj (measurableSet_singleton 0) (measure_ne_top _ _) (measure_ne_top _ _)
    rw [hunion, hsing, add_zero] at h
    rw [hIci]
    exact h.symm
  have huniv : Set.Iic (0:ℝ) ∪ Set.Ioi 0 = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ]
    by_cases h : x ≤ 0
    · exact iff_true_intro (Or.inl h)
    · exact iff_true_intro (Or.inr (not_le.mp h))
  have hdisj2 : Disjoint (Set.Iic (0:ℝ)) (Set.Ioi 0) := by
    rw [Set.disjoint_left]
    intro x hx h
    rw [Set.mem_Iic] at hx
    rw [Set.mem_Ioi] at h
    linarith
  have htot := measureReal_union (μ := gaussianReal 0 1) (s₁ := Set.Iic 0) (s₂ := Set.Ioi 0)
    hdisj2 measurableSet_Ioi (measure_ne_top _ _) (measure_ne_top _ _)
  rw [huniv] at htot
  have h1 : (gaussianReal 0 1).real Set.univ = 1 := by simp
  rw [h1, hIoi] at htot
  rw [cdf_eq_real]
  linarith

/-- Use: symmetry at `x = 1` in both directions. -/
example : cdf (gaussianReal 0 1) (-1) + cdf (gaussianReal 0 1) 1 = 1 := by
  rw [cdf_gaussianReal_neg]
  ring

/-- Boundary: at `x = 1` the cdf is strictly above `1 / 2`, so the identity is not vacuous. -/
example : cdf (gaussianReal 0 1) 0 < cdf (gaussianReal 0 1) 1 := by
  have hIoc := MathlibExt.Probability.CdfContinuityPoints.measure_Ioc_eq_ofReal_cdf
    (gaussianReal 0 1) 0 1
  have hvol : volume (Set.Ioc (0 : ℝ) 1) ≠ 0 := by
    rw [Real.volume_Ioc]
    simp
  have hac : volume ≪ gaussianReal (0 : ℝ) 1 :=
    gaussianReal_absolutelyContinuous' 0 one_ne_zero
  have hne : (gaussianReal 0 1) (Set.Ioc 0 1) ≠ 0 := fun h => hvol (hac h)
  have hpos : 0 < (gaussianReal 0 1) (Set.Ioc 0 1) := pos_iff_ne_zero.mpr hne
  rw [hIoc] at hpos
  rw [ENNReal.ofReal_pos] at hpos
  linarith

end MathlibExt.Probability.GaussianCdf
