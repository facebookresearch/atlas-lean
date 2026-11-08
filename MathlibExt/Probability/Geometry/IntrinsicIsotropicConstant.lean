/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.UniformBody
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Intrinsic affine spans for entropy-based isotropic constants

Source: `constants/20b.md` and Klartag--Lehec, arXiv:2412.15044v1,
Introduction after equation (1.4). Intrinsic dimension is positive; the
zero-dimensional convention is not assigned by a totalized formula.
-/

@[expose] public section

namespace MathlibExt.Probability.IsotropicConstant

open MeasureTheory
open scoped ENNReal

/-- An actual law in its actual affine span, with orthonormal intrinsic coordinates.
The map equality binds the ambient law to the density and entropy in coordinates. -/
structure IntrinsicLogConcaveLaw (ambient : ℕ) where
  dimension : ℕ
  coordinates : LogConcaveLaw dimension
  chart : EuclideanSpace ℝ (Fin dimension) →ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin ambient)
  law : Measure (EuclideanSpace ℝ (Fin ambient))
  law_eq : law = coordinates.law.map chart
  span_eq : Set.range chart =
    (affineSpan ℝ law.support : Set (EuclideanSpace ℝ (Fin ambient)))

theorem intrinsicLaw_probability {n : ℕ} (μ : IntrinsicLogConcaveLaw n) :
    IsProbabilityMeasure μ.law := by
  let : IsProbabilityMeasure μ.coordinates.law := μ.coordinates.probability
  rw [μ.law_eq]
  infer_instance

theorem intrinsicLaw_chart_measurable {n : ℕ} (μ : IntrinsicLogConcaveLaw n) :
    Measurable μ.chart := μ.chart.continuous.measurable

/-- Entropy and covariance are computed relative to the intrinsic affine span. -/
noncomputable def intrinsicLawIsotropicConstant {ambient : ℕ}
    (μ : IntrinsicLogConcaveLaw ambient) : ℝ :=
  lawIsotropicConstant μ.coordinates

/-- The actual ambient-dimensional family, including proper positive-dimensional affine spans. -/
noncomputable def dimensionIntrinsicLawSupremum (ambient : ℕ) : ℝ≥0∞ :=
  ⨆ μ : IntrinsicLogConcaveLaw ambient, ENNReal.ofReal (intrinsicLawIsotropicConstant μ)

/-- C20b with the entropy convention and actual intrinsic-span laws. -/
noncomputable def entropyIsotropicConstant : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), dimensionIntrinsicLawSupremum n

theorem intrinsicLawIsotropicConstant_le_dimensionSupremum {n : ℕ}
    (μ : IntrinsicLogConcaveLaw n) : ENNReal.ofReal (intrinsicLawIsotropicConstant μ) ≤
      dimensionIntrinsicLawSupremum n :=
  le_iSup (fun μ : IntrinsicLogConcaveLaw n =>
    ENNReal.ofReal (intrinsicLawIsotropicConstant μ)) μ

theorem dimensionIntrinsicLawSupremum_le_constant {n : ℕ} (hn : 0 < n) :
    dimensionIntrinsicLawSupremum n ≤ entropyIsotropicConstant :=
  le_iSup_of_le n (le_iSup (fun _ : 0 < n => dimensionIntrinsicLawSupremum n) hn)

/-- Each actual intrinsic representation contributes its actual coordinate entropy value. -/
theorem entropyIsotropicConstant_le_fullDimensionalSupremum :
    entropyIsotropicConstant ≤ fullDimensionalLawSupremum := by
  apply iSup_le
  intro n
  apply iSup_le
  intro _
  apply iSup_le
  intro μ
  exact (lawIsotropicConstant_le_dimensionSupremum μ.coordinates).trans
    (dimensionLawSupremum_le_fullSupremum μ.coordinates.dimension_pos)

/-- The actual affine span of a uniform full-dimensional body law is the whole space. -/
theorem bodyLaw_affineSpan_support {n : ℕ} (K : FullDimensionalBody n) :
    affineSpan ℝ (bodyLaw K).support = ⊤ := by
  have hv : volume.support = (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    Measure.support_eq_univ
  have hsub : interior (K.body : Set (EuclideanSpace ℝ (Fin n))) ⊆ (bodyLaw K).support := by
    intro x hx
    have hxs : x ∈ (volume.restrict (K.body : Set (EuclideanSpace ℝ (Fin n)))).support :=
      Measure.interior_inter_support ⟨hx, by simp [hv]⟩
    exact (Measure.absolutelyContinuous_smul
      (ENNReal.inv_ne_zero.mpr (bodyVolume_ne_top K))).support_mono hxs
  apply top_unique
  rw [← isOpen_interior.affineSpan_eq_top K.interior_nonempty]
  exact affineSpan_mono ℝ hsub

/-- Actual uniform body laws give intrinsic members via the identity orthonormal chart. -/
noncomputable def bodyIntrinsicLogConcaveLaw {n : ℕ} (K : FullDimensionalBody n) :
    IntrinsicLogConcaveLaw n where
  dimension := n
  coordinates := bodyLogConcaveLaw K
  chart := AffineIsometry.id
  law := bodyLaw K
  law_eq := by simp [bodyLogConcaveLaw]
  span_eq := by simp [bodyLaw_affineSpan_support K]

theorem bodyIntrinsicLaw_isotropicConstant {n : ℕ} (K : FullDimensionalBody n) :
    intrinsicLawIsotropicConstant (bodyIntrinsicLogConcaveLaw K) = bodyIsotropicConstant K :=
  bodyLogConcaveLaw_isotropicConstant K

theorem dimensionBodySupremum_le_intrinsicLawSupremum (n : ℕ) :
    dimensionBodySupremum n ≤ dimensionIntrinsicLawSupremum n := by
  apply iSup_le
  intro K
  rw [← bodyIntrinsicLaw_isotropicConstant K]
  exact intrinsicLawIsotropicConstant_le_dimensionSupremum (bodyIntrinsicLogConcaveLaw K)

theorem bodySupremum_le_entropyIsotropicConstant : bodySupremum ≤ entropyIsotropicConstant := by
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  exact (dimensionBodySupremum_le_intrinsicLawSupremum n).trans
    (dimensionIntrinsicLawSupremum_le_constant hn)

end MathlibExt.Probability.IsotropicConstant
