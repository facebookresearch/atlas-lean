/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ScalarGaussianCoordinates
public import MathlibExt.InformationTheory.VectorGaussianKL

/-!
# Kullback-Leibler divergence between real Gaussians

For real means `m₁`, `m₂` and positive variances `v₁`, `v₂` (variances, not standard deviations),
the Kullback-Leibler divergence, in nats, between the real Gaussians `N(m₁, v₁)` and `N(m₂, v₂)` is

`klDiv (N(m₁, v₁)) (N(m₂, v₂)) = ofReal ((log (v₂ / v₁) + (v₁ + (m₁ - m₂)²) / v₂ - 1) / 2)`.

The formula is the dimension-one case of the multivariate Gaussian divergence
`MathlibExt.InformationTheory.VectorGaussianKL.klDiv_multivariateGaussian`, transported along the
coordinate embedding `MathlibExt.InformationTheory.ScalarGaussianCoordinates.scalarCoord`; the
one-by-one determinant, inverse and trace reduce to the scalar expression.

Main results:
* `scalarGaussianKLReal`: the closed form above, as a real number.
* `scalarGaussianKLReal_eq_multivariateGaussianKLReal`: the scalar closed form is the vector closed
  form at dimension one, for all real parameters.
* `klDiv_gaussianReal`: the divergence formula for positive `ℝ≥0` variances, and
  `klDiv_gaussianReal_of_pos`, the same formula for real variances with positivity proofs.
* `klDiv_gaussianReal_self`, `klDiv_gaussianReal_same_variance`: equal laws give `0`, and a common
  variance `v` gives `(m₁ - m₂)² / (2 v)`.
* `klDiv_gaussianReal_zero_variance`, `klDiv_gaussianReal_zero_variance_ne`: a zero first variance
  gives `∞`, which the finite closed form does not match, so the positivity hypothesis is needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp InformationTheory
open scoped ENNReal NNReal

namespace MathlibExt.InformationTheory.ScalarGaussianKL

open MathlibExt.InformationTheory.VectorGaussianKL
open MathlibExt.InformationTheory.ScalarGaussianCoordinates

/-- The scalar Gaussian divergence closed form, in nats:
`(log (v₂ / v₁) + (v₁ + (m₁ - m₂)²) / v₂ - 1) / 2`. -/
noncomputable def scalarGaussianKLReal (m₁ m₂ v₁ v₂ : ℝ) : ℝ :=
  (Real.log (v₂ / v₁) + (v₁ + (m₁ - m₂) ^ 2) / v₂ - 1) / 2

/-- The scalar closed form is the vector closed form at dimension one, read through the coordinate
embedding: the one-by-one determinant, inverse and trace simplify to the scalar expression.
An identity for all real parameters. -/
theorem scalarGaussianKLReal_eq_multivariateGaussianKLReal (m₁ m₂ v₁ v₂ : ℝ) :
    scalarGaussianKLReal m₁ m₂ v₁ v₂ =
      multivariateGaussianKLReal (scalarCoord m₁) (scalarCoord m₂)
        (!![v₁] : Matrix (Fin 1) (Fin 1) ℝ) (!![v₂] : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hcoord : ∀ m : ℝ, scalarCoord m = toLp 2 ![m] := fun m => by
    ext i
    fin_cases i
    simp
  rw [hcoord, hcoord, multivariateGaussianKLReal_fin_one]
  unfold scalarGaussianKLReal
  ring

/-- **Scalar Gaussian divergence.** For real means and positive nonnegative-real variances,
`klDiv (N(m₁, v₁)) (N(m₂, v₂)) = ofReal ((log (v₂ / v₁) + (v₁ + (m₁ - m₂)²) / v₂ - 1) / 2)`. -/
theorem klDiv_gaussianReal (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    klDiv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂) =
      ENNReal.ofReal (scalarGaussianKLReal m₁ m₂ v₁ v₂) := by
  obtain ⟨v₁, hv₁'⟩ := v₁
  obtain ⟨v₂, hv₂'⟩ := v₂
  have h := scalarGaussian_klDiv_eq_vector m₁ m₂ v₁ v₂ (NNReal.coe_pos.mpr hv₁)
    (NNReal.coe_pos.mpr hv₂)
  rw [← scalarGaussianKLReal_eq_multivariateGaussianKLReal] at h
  exact h

/-- Real-parameter form of `klDiv_gaussianReal`, in the variance packaging of
`scalarGaussian_klDiv_eq_vector`: variances `s`, `t : ℝ` with `0 < s`, `0 < t`. -/
theorem klDiv_gaussianReal_of_pos (m₁ m₂ s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    klDiv (gaussianReal m₁ ⟨s, hs.le⟩) (gaussianReal m₂ ⟨t, ht.le⟩) =
      ENNReal.ofReal (scalarGaussianKLReal m₁ m₂ s t) :=
  klDiv_gaussianReal m₁ m₂ ⟨s, hs.le⟩ ⟨t, ht.le⟩ (NNReal.coe_pos.mp hs) (NNReal.coe_pos.mp ht)

/-- Validation, equal laws, closed form: the closed form vanishes at equal means and a common
nonzero variance. -/
theorem scalarGaussianKLReal_self (m v : ℝ) (hv : v ≠ 0) :
    scalarGaussianKLReal m m v v = 0 := by
  simp [scalarGaussianKLReal, div_self hv]

/-- Validation, equal laws: the divergence of a positive-variance Gaussian from itself is zero, and
the headline closed form agrees. -/
theorem klDiv_gaussianReal_self (m : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    klDiv (gaussianReal m v) (gaussianReal m v) = 0 ∧
      ENNReal.ofReal (scalarGaussianKLReal m m v v) = 0 := by
  refine ⟨klDiv_self _, ?_⟩
  rw [scalarGaussianKLReal_self m (v : ℝ) (NNReal.coe_pos.mpr hv).ne', ENNReal.ofReal_zero]

/-- Validation, shifted equal variance, closed form: at a common nonzero variance `v` the closed
form is `(m₁ - m₂)² / (2 v)`. -/
theorem scalarGaussianKLReal_same_variance (m₁ m₂ v : ℝ) (hv : v ≠ 0) :
    scalarGaussianKLReal m₁ m₂ v v = (m₁ - m₂) ^ 2 / (2 * v) := by
  unfold scalarGaussianKLReal
  rw [div_self hv, Real.log_one]
  field_simp
  ring

/-- Validation, shifted equal variance: `klDiv (N(m₁, v)) (N(m₂, v)) = ofReal ((m₁ - m₂)² / (2 v))`
for a positive variance `v`. -/
theorem klDiv_gaussianReal_same_variance (m₁ m₂ : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    klDiv (gaussianReal m₁ v) (gaussianReal m₂ v) =
      ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * (v : ℝ))) := by
  rw [klDiv_gaussianReal m₁ m₂ v v hv hv,
    scalarGaussianKLReal_same_variance m₁ m₂ (v : ℝ) (NNReal.coe_pos.mpr hv).ne']

/-- Boundary, zero first variance: `N(m₁, 0)` is a point mass, which is not absolutely continuous
with respect to a positive-variance Gaussian, so the divergence is `∞`. -/
theorem klDiv_gaussianReal_zero_variance (m₁ m₂ : ℝ) (v₂ : ℝ≥0) (hv₂ : 0 < v₂) :
    klDiv (gaussianReal m₁ 0) (gaussianReal m₂ v₂) = ∞ := by
  rw [gaussianReal_zero_var]
  apply klDiv_of_not_ac
  intro h
  have : NullSingletonClass (gaussianReal m₂ v₂) := nullSingletonClass_gaussianReal hv₂.ne'
  have h1 : Measure.dirac m₁ {m₁} = 0 := h (measure_singleton m₁)
  rw [Measure.dirac_apply_of_mem (Set.mem_singleton m₁)] at h1
  exact one_ne_zero h1

/-- Boundary, zero first variance: the density formula does not extend to `v₁ = 0`; the finite
closed form differs from the divergence there, so the positivity hypothesis cannot be dropped. -/
theorem klDiv_gaussianReal_zero_variance_ne (m₁ m₂ : ℝ) (v₂ : ℝ≥0) (hv₂ : 0 < v₂) :
    klDiv (gaussianReal m₁ 0) (gaussianReal m₂ v₂) ≠
      ENNReal.ofReal (scalarGaussianKLReal m₁ m₂ 0 v₂) := by
  rw [klDiv_gaussianReal_zero_variance m₁ m₂ v₂ hv₂]
  exact ENNReal.ofReal_ne_top.symm

end MathlibExt.InformationTheory.ScalarGaussianKL
