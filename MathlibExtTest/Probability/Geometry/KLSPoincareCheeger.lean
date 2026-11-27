/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Geometry.KLSPoincareCheeger
import MathlibExt.Probability.Geometry.UniformInterval

open MeasureTheory
open scoped ENNReal
open MathlibExt.Probability.ThinShell
open MathlibExt.Probability.KLS

-- Cheeger's inequality for the isotropic uniform law on `[-√3, √3]`, a one-dimensional isotropic
-- log-concave measure, called with the named hypothesis of the statement.
example : smoothPoincareConstant (uniformInterval (Real.sqrt 3)) ≤
    4 * inverseCheegerConstant (uniformInterval (Real.sqrt 3)) ^ 2 :=
  poincare_cheeger_upper_bound (hn := by decide) uniformInterval_sqrt_three_isIsotropicLogConcave

-- Cheeger's inequality needs no isotropy: the uniform law on `[-1, 1]` has variance `1/3`.
example : smoothPoincareConstant (uniformInterval 1) ≤
    4 * inverseCheegerConstant (uniformInterval 1) ^ 2 :=
  haveI := uniformInterval_probability one_pos
  smoothPoincareConstant_le_four_mul_inverseCheegerConstant_sq _

-- Nor log-concavity, nor a positive dimension: the average of the Dirac masses at two points of
-- `ℝⁿ`, which is not log-concave when the points differ, in every dimension, including `n = 0`.
example {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    smoothPoincareConstant ((2⁻¹ : ℝ≥0∞) • (Measure.dirac x + Measure.dirac y)) ≤
      4 * inverseCheegerConstant ((2⁻¹ : ℝ≥0∞) • (Measure.dirac x + Measure.dirac y)) ^ 2 := by
  have : IsProbabilityMeasure ((2⁻¹ : ℝ≥0∞) • (Measure.dirac x + Measure.dirac y)) :=
    ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  exact smoothPoincareConstant_le_four_mul_inverseCheegerConstant_sq _

-- With the KLS constant, the smooth Poincaré constant of every isotropic log-concave measure is
-- at most `4 ψ²`, where `ψ` is the KLS constant: a dimension-free Poincaré bound whenever the KLS
-- conjecture holds.
example {n : ℕ} (hn : 0 < n) {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : IsIsotropicLogConcave μ) : smoothPoincareConstant μ ≤ 4 * klsConstant ^ 2 := by
  refine (poincare_cheeger_upper_bound hn hμ).trans ?_
  gcongr
  exact inverseCheegerConstant_le_constant hn hμ

-- A finite KLS constant bounds all smooth Poincaré constants of isotropic log-concave measures
-- by one finite constant.
example (h : klsConstant < ⊤) : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ, 0 < n →
    ∀ μ : Measure (EuclideanSpace ℝ (Fin n)), IsIsotropicLogConcave μ →
      smoothPoincareConstant μ ≤ C := by
  refine ⟨4 * klsConstant ^ 2, ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top h),
    fun n hn μ hμ => (poincare_cheeger_upper_bound hn hμ).trans ?_⟩
  gcongr
  exact inverseCheegerConstant_le_constant hn hμ
