/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.ThinShell
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Entropy-based isotropic constants

Source: `constants/20b.md` and Klartag--Lehec, arXiv:2412.15044v1,
Introduction, equations (1.2)--(1.6). Entropy uses natural logarithms.
-/

@[expose] public section

namespace MathlibExt.Probability.IsotropicConstant

open MeasureTheory
open scoped ENNReal
open scoped BigOperators

/-- The actual covariance matrix of the coordinate random variables.
Source: `constants/20b.md`, covariance definition. -/
noncomputable def covarianceMatrix {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ProbabilityTheory.covariance (fun x => x i) (fun x => x j) μ

/-- Differential entropy of a Lebesgue density, using the actual entropy integral.
Source: `constants/20b.md`, Ent(μ)=-∫f log f. -/
noncomputable def differentialEntropy {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  -(∫ x, f x * Real.log (f x))

/-- A full-dimensional convex body in a positive-dimensional Euclidean space.
Source: `constants/20b.md`, convex-body domain. -/
structure FullDimensionalBody (n : ℕ) where
  body : ConvexBody (EuclideanSpace ℝ (Fin n))
  dimension_pos : 0 < n
  interior_nonempty : (interior (body : Set (EuclideanSpace ℝ (Fin n)))).Nonempty

/-- A genuine log-concave probability law and its Lebesgue density.
Source: `constants/20b.md`; finite moments and entropy integrability ensure the
displayed real integrals do not use the non-integrable default value. -/
structure LogConcaveLaw (n : ℕ) where
  dimension_pos : 0 < n
  law : Measure (EuclideanSpace ℝ (Fin n))
  probability : IsProbabilityMeasure law
  density : EuclideanSpace ℝ (Fin n) → ℝ
  logConcave : ThinShell.IsLogConcaveDensity density
  law_eq : law = volume.withDensity (fun x => ENNReal.ofReal (density x))
  moment_one : ∀ i : Fin n, Integrable (fun x => x i) law
  moment_two : ∀ i j : Fin n, Integrable (fun x => x i * x j) law
  entropy_integrable : Integrable (fun x => density x * Real.log (density x)) volume

/-- Actual covariance is positive semidefinite, by integrating squared linear forms. -/
theorem covarianceMatrix_posSemidef {n : ℕ} (μ : LogConcaveLaw n) :
    (covarianceMatrix μ.law).PosSemidef := by
  let : IsProbabilityMeasure μ.law := μ.probability
  let m : Fin n → ℝ := fun i => ∫ x, x i ∂μ.law
  have hc : ∀ i j : Fin n, Integrable (fun x => (x i - m i) * (x j - m j)) μ.law := by
    intro i j
    convert (((μ.moment_two i j).sub ((μ.moment_one i).mul_const (m j))).sub
      ((μ.moment_one j).const_mul (m i))).add (integrable_const (m i * m j)) using 1
    ext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hHerm : (covarianceMatrix μ.law).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, covarianceMatrix, star_trivial,
      ProbabilityTheory.covariance_comm]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  have hcv : ∀ i j : Fin n,
      Integrable (fun x => v i * (((x i - m i) * (x j - m j)) * v j)) μ.law := by
    intro i j
    exact ((hc i j).mul_const (v j)).const_mul (v i)
  have hs : ∀ i : Fin n, Integrable
      (fun x => ∑ j : Fin n, v i * (((x i - m i) * (x j - m j)) * v j)) μ.law := by
    intro i
    exact integrable_finsetSum Finset.univ (fun j _ => hcv i j)
  have hinner (i : Fin n) :
      (∑ j : Fin n, ∫ x, v i * (((x i - m i) * (x j - m j)) * v j) ∂μ.law) =
        ∫ x, ∑ j : Fin n, v i * (((x i - m i) * (x j - m j)) * v j) ∂μ.law :=
    (integral_finsetSum Finset.univ (fun j _ => hcv i j)).symm
  have heq : star v ⬝ᵥ (covarianceMatrix μ.law).mulVec v =
      ∫ x, (∑ i : Fin n, v i * (x i - m i)) ^ 2 ∂μ.law := by
    simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, covarianceMatrix,
      ProbabilityTheory.covariance]
    simp_rw [Finset.mul_sum, ← integral_mul_const, ← integral_const_mul]
    change (∑ i : Fin n, ∑ j : Fin n,
      ∫ x, v i * (((x i - m i) * (x j - m j)) * v j) ∂μ.law) = _
    simp_rw [hinner]
    rw [← integral_finsetSum Finset.univ (fun i _ => hs i)]
    congr 1
    ext x
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    congr 1
    ext i
    congr 1
    ext j
    ring
  rw [heq]
  apply integral_nonneg
  intro x
  positivity

theorem covarianceMatrix_det_nonneg {n : ℕ} (μ : LogConcaveLaw n) :
    0 ≤ (covarianceMatrix μ.law).det :=
  (covarianceMatrix_posSemidef μ).det_nonneg

/-- The shared probabilistic isotropy convention gives the actual identity covariance. -/
theorem covarianceMatrix_eq_one_of_isIsotropic {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : ThinShell.IsIsotropicLogConcave μ) :
    covarianceMatrix μ = 1 := by
  ext i j
  simp only [covarianceMatrix, ProbabilityTheory.covariance, (hμ.2.2.1 i).2,
    (hμ.2.2.1 j).2, sub_zero, Matrix.one_apply]
  exact (hμ.2.2.2 i j).2

/-- Actual normalized Lebesgue volume on a full-dimensional convex body. -/
noncomputable def bodyLaw {n : ℕ} (K : FullDimensionalBody n) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  ProbabilityTheory.cond volume (K.body : Set (EuclideanSpace ℝ (Fin n)))

/-- The determinant-and-volume convention for convex bodies. -/
noncomputable def bodyIsotropicConstant {n : ℕ} (K : FullDimensionalBody n) : ℝ :=
  Real.rpow ((covarianceMatrix (bodyLaw K)).det /
    (volume (K.body : Set (EuclideanSpace ℝ (Fin n)))).toReal ^ 2)
    (1 / (2 * (n : ℝ)))

/-- The entropy convention for actual log-concave laws. -/
noncomputable def lawIsotropicConstant {n : ℕ} (μ : LogConcaveLaw n) : ℝ :=
  Real.exp (-differentialEntropy μ.density / (n : ℝ)) *
    Real.rpow (covarianceMatrix μ.law).det (1 / (2 * (n : ℝ)))

/-- The supremum over actual full-dimensional convex bodies in dimension n. -/
noncomputable def dimensionBodySupremum (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : FullDimensionalBody n, ENNReal.ofReal (bodyIsotropicConstant K)

/-- The supremum over actual full-dimensional laws with integrable entropy. -/
noncomputable def dimensionLawSupremum (n : ℕ) : ℝ≥0∞ :=
  ⨆ μ : LogConcaveLaw n, ENNReal.ofReal (lawIsotropicConstant μ)

/-- The sharp-value body constant from `constants/20b.md`. -/
noncomputable def bodySupremum : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), dimensionBodySupremum n

/-- The centered symmetry convention `K = -K` used by the sharp body conjecture.
Source: arXiv:2412.15044v1, Introduction after Theorem 1.2. -/
def IsCentrallySymmetric {n : ℕ} (K : FullDimensionalBody n) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    x ∈ (K.body : Set (EuclideanSpace ℝ (Fin n))) ↔
      -x ∈ (K.body : Set (EuclideanSpace ℝ (Fin n)))

/-- The actual body supremum restricted to bodies symmetric about the origin. -/
noncomputable def centrallySymmetricBodySupremum : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), ⨆ K : FullDimensionalBody n,
    ⨆ (_ : IsCentrallySymmetric K), ENNReal.ofReal (bodyIsotropicConstant K)

/-- The squared-radius thin-shell convention in KL2022 and JLV2022.
This is not the radius-fluctuation width used elsewhere in the catalogue. -/
noncomputable def squaredRadiusThinShellWidth (n : ℕ) : ℝ≥0∞ :=
  ⨆ μ : Measure (EuclideanSpace ℝ (Fin n)), ⨆ (_ : ThinShell.IsIsotropicLogConcave μ),
    ENNReal.rpow (ThinShell.normalizedRadiusVariance μ) (1 / 2)

/-- The full-dimensional entropy-law supremum. Proper affine spans require the
separately tracked intrinsic-coordinate bridge. -/
noncomputable def fullDimensionalLawSupremum : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), dimensionLawSupremum n

theorem bodyIsotropicConstant_le_dimensionSupremum {n : ℕ} (K : FullDimensionalBody n) :
    ENNReal.ofReal (bodyIsotropicConstant K) ≤ dimensionBodySupremum n :=
  le_iSup (fun K : FullDimensionalBody n => ENNReal.ofReal (bodyIsotropicConstant K)) K

theorem lawIsotropicConstant_le_dimensionSupremum {n : ℕ} (μ : LogConcaveLaw n) :
    ENNReal.ofReal (lawIsotropicConstant μ) ≤ dimensionLawSupremum n :=
  le_iSup (fun μ : LogConcaveLaw n => ENNReal.ofReal (lawIsotropicConstant μ)) μ

theorem dimensionBodySupremum_le_bodySupremum {n : ℕ} (hn : 0 < n) :
    dimensionBodySupremum n ≤ bodySupremum :=
  le_iSup_of_le n (le_iSup (fun _ : 0 < n => dimensionBodySupremum n) hn)

theorem symmetricBodyIsotropicConstant_le_supremum {n : ℕ}
    (K : FullDimensionalBody n) (hK : IsCentrallySymmetric K) :
    ENNReal.ofReal (bodyIsotropicConstant K) ≤ centrallySymmetricBodySupremum :=
  le_iSup_of_le n (le_iSup_of_le K.dimension_pos (le_iSup_of_le K
    (le_iSup (fun _ : IsCentrallySymmetric K =>
      ENNReal.ofReal (bodyIsotropicConstant K)) hK)))

theorem squaredRadiusThinShellWidth_le_varianceConstant (n : ℕ) (hn : 0 < n) :
    squaredRadiusThinShellWidth n ≤ ENNReal.rpow ThinShell.thinShellVarianceConstant (1 / 2) := by
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  exact ENNReal.rpow_le_rpow (ThinShell.normalizedRadiusVariance_le_constant hn hμ)
    (by norm_num)

theorem dimensionLawSupremum_le_fullSupremum {n : ℕ} (hn : 0 < n) :
    dimensionLawSupremum n ≤ fullDimensionalLawSupremum :=
  le_iSup_of_le n (le_iSup (fun _ : 0 < n => dimensionLawSupremum n) hn)

end MathlibExt.Probability.IsotropicConstant
