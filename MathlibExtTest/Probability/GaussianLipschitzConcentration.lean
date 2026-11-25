/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.GaussianLipschitzConcentration
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Tests for the concentration of Lipschitz functions of a standard Gaussian vector

* A linear form `x ↦ ⟪u, x⟫` is `‖u‖`-Lipschitz and centred, so the theorem gives the
  sub-Gaussian parameter `‖u‖²`, which is exact: `⟪u, X⟫` is a centred Gaussian variable of
  variance `‖u‖²`.
* The Euclidean norm is `1`-Lipschitz: `‖X‖` concentrates around its mean with a tail bound that
  does not depend on the dimension, for instance `P(|‖X‖ - E‖X‖| ≥ 3) ≤ 2 exp (-9 / 2)`.
* The distance to a fixed set is `1`-Lipschitz, so it concentrates in the same way.
* A scaled norm `x ↦ 3 ‖x‖` is `3`-Lipschitz, with tail bound `2 exp (-t² / 18)`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal RealInnerProductSpace
open MathlibExt.Probability.HighDimensionalStatisticsWanted

namespace MathlibExtTest.Probability.GaussianLipschitzConcentration

/-- A linear form `x ↦ ⟪u, x⟫` is centred and sub-Gaussian with variance proxy `‖u‖²`, the
exact variance of the Gaussian variable `⟪u, X⟫`. -/
example {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    HasSubgaussianMGF (fun x ↦ ⟪u, x⟫) (‖u‖₊ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hL : LipschitzWith ‖u‖₊ fun x : EuclideanSpace ℝ (Fin n) ↦ ⟪u, x⟫ := by
    have h := (innerSL ℝ u).lipschitzWith
    rwa [show ‖innerSL ℝ u‖₊ = ‖u‖₊ from NNReal.eq (innerSL_apply_norm ℝ u)] at h
  have hmean : ∫ y, ⟪u, y⟫ ∂stdGaussian (EuclideanSpace ℝ (Fin n)) = 0 := by
    simpa using integral_strongDual_stdGaussian (innerSL ℝ u)
  simpa [hmean] using (lipschitz_concentration_stdGaussian hL).1

/-- The Euclidean norm of a standard Gaussian vector is sub-Gaussian with variance proxy `1`
about its mean, in every dimension. -/
example {n : ℕ} :
    HasSubgaussianMGF (fun x ↦ ‖x‖ - ∫ y, ‖y‖ ∂stdGaussian (EuclideanSpace ℝ (Fin n))) 1
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  simpa using (lipschitz_concentration_stdGaussian (lipschitzWith_one_norm (E :=
    EuclideanSpace ℝ (Fin n)))).1

/-- A dimension-free tail bound for the Euclidean norm: `P(|‖X‖ - E‖X‖| ≥ 3) ≤ 2 exp (-9 / 2)`,
which is less than `0.03`. -/
example {n : ℕ} :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {x | 3 ≤ |‖x‖ - ∫ y, ‖y‖ ∂stdGaussian (EuclideanSpace ℝ (Fin n))|} ≤
      2 * exp (-9 / 2) := by
  have h := (lipschitz_concentration_stdGaussian (lipschitzWith_one_norm (E :=
    EuclideanSpace ℝ (Fin n)))).2 3 (by norm_num)
  norm_num at h ⊢
  exact h

/-- The distance from a standard Gaussian vector to a fixed set concentrates around its mean. -/
example {n : ℕ} (s : Set (EuclideanSpace ℝ (Fin n))) {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {x | t ≤ |Metric.infDist x s -
          ∫ y, Metric.infDist y s ∂stdGaussian (EuclideanSpace ℝ (Fin n))|} ≤
      2 * exp (-t ^ 2 / 2) := by
  simpa using (lipschitz_concentration_stdGaussian (Metric.lipschitz_infDist_pt s)).2 t ht

/-- A `3`-Lipschitz function: the tail bound reads `2 exp (-t² / 18)`. -/
example {n : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {x | t ≤ |3 * ‖x‖ - ∫ y, 3 * ‖y‖ ∂stdGaussian (EuclideanSpace ℝ (Fin n))|} ≤
      2 * exp (-t ^ 2 / 18) := by
  have hL : LipschitzWith 3 fun x : EuclideanSpace ℝ (Fin n) ↦ 3 * ‖x‖ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, ← mul_sub, abs_mul, dist_eq_norm]
    norm_num
    exact abs_norm_sub_norm_le x y
  have h := (lipschitz_concentration_stdGaussian hL).2 t ht
  norm_num at h ⊢
  exact h

end MathlibExtTest.Probability.GaussianLipschitzConcentration
