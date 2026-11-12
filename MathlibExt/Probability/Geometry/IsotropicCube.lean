/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.IntrinsicIsotropicConstant
public import MathlibExt.Probability.Geometry.UniformInterval

/-!
# The actual one-dimensional volume-one cube

Source: `constants/20b.md`, the cube [-1/2,1/2] and the global lower bound
1/√12. Its Lebesgue law is computed, not postulated.
-/

@[expose] public section

namespace MathlibExt.Probability.IsotropicConstant

open MeasureTheory
open ThinShell
open scoped ENNReal

/-- **Symmetric interval as a convex body.** For a real number $a > 0$, this is the closed
interval $[-a, a]$ in the one-dimensional Euclidean space, regarded as a full-dimensional convex
body. -/
noncomputable def intervalBody (a : ℝ) (ha : 0 < a) : FullDimensionalBody 1 where
  body := {
    carrier := symmetricInterval a
    convex' := symmetricInterval_convex a
    isCompact' := by
      convert (isCompact_Icc : IsCompact (Set.Icc (-a) a)).image
        lineIsometry.continuous using 1
      ext x
      constructor
      · intro hx
        exact ⟨lineIsometry.symm x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [symmetricInterval] using hy
    nonempty' := ⟨lineIsometry 0, by simp [symmetricInterval, ha.le]⟩
  }
  dimension_pos := by decide
  interior_nonempty := by
    have hopen : IsOpen (lineIsometry.symm ⁻¹' Set.Ioo (-a) a) :=
      isOpen_Ioo.preimage lineIsometry.symm.continuous
    have hsub : lineIsometry.symm ⁻¹' Set.Ioo (-a) a ⊆ symmetricInterval a :=
      Set.preimage_mono Set.Ioo_subset_Icc_self
    exact ⟨lineIsometry 0, interior_maximal hsub hopen (by simp [ha])⟩

theorem intervalBody_law (a : ℝ) (ha : 0 < a) :
    bodyLaw (intervalBody a ha) = uniformInterval a := rfl

theorem interval_covariance_det {a : ℝ} (ha : 0 < a) :
    (covarianceMatrix (uniformInterval a)).det = a ^ 2 / 3 := by
  rw [Matrix.det_fin_one]
  simp only [covarianceMatrix, ProbabilityTheory.covariance, uniformInterval_mean ha.le,
    sub_zero]
  exact uniformInterval_secondMoment ha 0 0

/-- **Unit interval body.** The unit interval body is the closed interval $[-1/2, 1/2]$, of length
one and centred at the origin, in the one-dimensional Euclidean space, regarded as a
full-dimensional convex body. -/
noncomputable def unitIntervalBody : FullDimensionalBody 1 :=
  intervalBody (1 / 2) (by norm_num)

theorem unitIntervalBody_volume :
    volume (unitIntervalBody.body : Set (EuclideanSpace ℝ (Fin 1))) = 1 := by
  change volume (symmetricInterval (1 / 2)) = 1
  rw [symmetricInterval_volume]
  norm_num

theorem unitIntervalBody_covariance_det :
    (covarianceMatrix (bodyLaw unitIntervalBody)).det = 1 / 12 := by
  change (covarianceMatrix (uniformInterval (1 / 2))).det = 1 / 12
  rw [interval_covariance_det (by norm_num)]
  norm_num

theorem unitIntervalBody_entropy : differentialEntropy (bodyDensity unitIntervalBody) = 0 := by
  rw [bodyDensity_entropy, unitIntervalBody_volume]
  simp

theorem unitIntervalBody_isotropicConstant : bodyIsotropicConstant unitIntervalBody =
    1 / Real.sqrt 12 := by
  rw [bodyIsotropicConstant, unitIntervalBody_covariance_det, unitIntervalBody_volume]
  simp only [ENNReal.toReal_one, one_pow, div_one, Nat.cast_one]
  norm_num only [mul_one]
  rw [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num)]
  simp

/-- **Cube lower bound for the supremal isotropic constant.** The supremum, over all positive
integers $n$ and all full-dimensional convex bodies $K \subseteq \mathbb{R}^n$, of the isotropic
constant $L_K = \left(\det \mathrm{Cov}(K) / \mathrm{Vol}(K)^2\right)^{1/(2n)}$, where
$\mathrm{Cov}(K)$ is the covariance matrix of the uniform distribution on $K$, is at least
$1/\sqrt{12}$.

The interval $[-1/2, 1/2]$ in dimension one already attains $L_K = 1/\sqrt{12}$. -/
theorem inv_sqrt_twelve_le_bodySupremum :
    ENNReal.ofReal (1 / Real.sqrt 12) ≤ bodySupremum := by
  rw [← unitIntervalBody_isotropicConstant]
  exact (bodyIsotropicConstant_le_dimensionSupremum unitIntervalBody).trans
    (dimensionBodySupremum_le_bodySupremum (by decide))

theorem inv_sqrt_twelve_le_entropyIsotropicConstant :
    ENNReal.ofReal (1 / Real.sqrt 12) ≤ entropyIsotropicConstant :=
  inv_sqrt_twelve_le_bodySupremum.trans bodySupremum_le_entropyIsotropicConstant

/-- **Membership in the unit interval body.** A point $x$ of the one-dimensional Euclidean space
lies in the unit interval body if and only if its single coordinate $x_1$ satisfies
$-1/2 \le x_1 \le 1/2$. -/
theorem unitIntervalBody_mem_iff (x : EuclideanSpace ℝ (Fin 1)) :
    x ∈ (unitIntervalBody.body : Set (EuclideanSpace ℝ (Fin 1))) ↔
      ∀ i : Fin 1, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ (1 / 2 : ℝ) := by
  have hc (i : Fin 1) : lineIsometry.symm x = x i := by
    have h := lineIsometry_apply (lineIsometry.symm x) i
    simpa using h.symm
  change lineIsometry.symm x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ↔ _
  constructor
  · intro h i
    simpa only [Set.mem_Icc, hc i] using h
  · intro h
    simpa only [Set.mem_Icc, hc 0] using h 0

theorem unitIntervalBody_isCentrallySymmetric : IsCentrallySymmetric unitIntervalBody := by
  intro x
  rw [unitIntervalBody_mem_iff, unitIntervalBody_mem_iff]
  constructor
  · intro hx i
    exact ⟨by simpa using neg_le_neg (hx i).2, by simpa using neg_le_neg (hx i).1⟩
  · intro hx i
    exact ⟨by simpa using neg_le_neg (hx i).2, by simpa using neg_le_neg (hx i).1⟩

theorem inv_sqrt_twelve_le_centrallySymmetricBodySupremum :
    ENNReal.ofReal (1 / Real.sqrt 12) ≤ centrallySymmetricBodySupremum := by
  rw [← unitIntervalBody_isotropicConstant]
  exact symmetricBodyIsotropicConstant_le_supremum unitIntervalBody
    unitIntervalBody_isCentrallySymmetric

end MathlibExt.Probability.IsotropicConstant
