/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Real-interval Uniform moment consumers

Named private declarations retain positive, arbitrary-domain and degenerate-interval
consumers for full private trust audit and replay. No probability instance is assumed in
the generic API consumers. Conditioning Lebesgue measure on a singleton produces zero,
not a Dirac probability measure, so the strict interval hypothesis must not be erased.
-/

open MeasureTheory ProbabilityTheory Set
open MeasureTheory.pdf

namespace MathlibExtTest.Probability.Distributions.Uniform

private theorem unit_interval_law :
    IsUniform (id : ℝ → ℝ) (Icc 0 1) (volume[|Icc 0 1]) :=
  IsUniform.cond

private theorem unit_interval_mean : (∫ x, x ∂volume[|Icc (0 : ℝ) 1]) = 1 / 2 := by
  simpa using IsUniform.integral_of_Icc (by norm_num) unit_interval_law

private theorem unit_interval_second_moment :
    (∫ x, x ^ (2 : ℕ) ∂volume[|Icc (0 : ℝ) 1]) = 1 / 3 := by
  have h := IsUniform.integral_pow_of_Icc (by norm_num) unit_interval_law 2
  norm_num at h
  exact h

private theorem unit_interval_variance : Var[id; volume[|Icc (0 : ℝ) 1]] = 1 / 12 := by
  simpa using IsUniform.variance_of_Icc (by norm_num) unit_interval_law

private theorem asymmetric_interval_law :
    IsUniform (id : ℝ → ℝ) (Icc (-1) 3) (volume[|Icc (-1) 3]) :=
  IsUniform.cond

private theorem asymmetric_interval_mean : (∫ x, x ∂volume[|Icc (-1 : ℝ) 3]) = 1 := by
  have h := IsUniform.integral_of_Icc (by norm_num) asymmetric_interval_law
  norm_num at h ⊢
  exact h

private theorem asymmetric_interval_variance : Var[id; volume[|Icc (-1 : ℝ) 3]] = 4 / 3 := by
  have h := IsUniform.variance_of_Icc (by norm_num) asymmetric_interval_law
  norm_num at h ⊢
  exact h

private theorem arbitrary_domain_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {a b : ℝ} (hab : a < b) (hu : IsUniform X (Icc a b) P) (k : ℕ) :
    ∫ ω, X ω ^ k ∂P = (b ^ (k + 1) - a ^ (k + 1)) / ((k + 1) * (b - a)) :=
  hu.integral_pow_of_Icc hab k

private theorem arbitrary_domain_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {a b : ℝ} (hab : a < b) (hu : IsUniform X (Icc a b) P) :
    Var[X; P] = (b - a) ^ 2 / 12 :=
  hu.variance_of_Icc hab

private theorem singleton_cond_eq_zero : volume[|Icc (1 : ℝ) 1] = 0 := by
  apply ProbabilityTheory.cond_eq_zero.mpr
  right
  simp

/-- The Uniform predicate really holds for the degenerate interval under zero measure. -/
private theorem singleton_zero_law : IsUniform (id : ℝ → ℝ) (Icc 1 1) (0 : Measure ℝ) := by
  rw [← singleton_cond_eq_zero]
  exact IsUniform.cond

private theorem singleton_zero_mean_counterexample :
    (∫ x : ℝ, x ∂(0 : Measure ℝ)) ≠ ((1 : ℝ) + 1) / 2 := by
  norm_num

/-- Even restricting to canonical conditional laws, the unrestricted mean claim is false. -/
private theorem uniform_mean_without_strict_endpoints_is_false :
    ¬ (∀ a b : ℝ, ∀ P : Measure ℝ,
      IsUniform (id : ℝ → ℝ) (Icc a b) P → (∫ x, x ∂P) = (a + b) / 2) := by
  intro h
  exact singleton_zero_mean_counterexample (h 1 1 0 singleton_zero_law)

-- At equal endpoints the variance formula agrees only by junk: zero measure and zero width
-- both give zero. It is not a variance counterexample or a probability interpretation.
private theorem singleton_zero_variance_junk_agreement :
    Var[id; (0 : Measure ℝ)] = ((1 : ℝ) - 1) ^ 2 / 12 := by
  simp [ProbabilityTheory.variance, ProbabilityTheory.evariance]

end MathlibExtTest.Probability.Distributions.Uniform
