/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.TrueScore
public import MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables

/-!
# Reliability of a sum (Spearman-Brown)

In a parallel measurement model, the reliability of the sum score is the
Spearman-Brown expression in the one-item reliability.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
open scoped MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- **Spearman-Brown formula for the reliability of a sum.**
In the parallel model `X j = T + E j` (`k >= 1` items, common true
score `T`, errors uncorrelated with `T` and mutually uncorrelated,
every error of variance `w`, `Var[T] = v > 0`, `w >= 0`), the
reliability of the sum, `Var[k * T] / Var[sum X]`, is the
Spearman-Brown expression `k * rho / (1 + (k - 1) * rho)` in the
one-item reliability `rho = attenuationFactor v w = v / (v + w)`.

This is the Spearman-Brown prophecy formula for the reliability of a
lengthened test: Spearman, "Correlation calculated from faulty data",
British Journal of Psychology 3 (1910), 271-295, and Brown, "Some
experimental results in the correlation of mental abilities", British
Journal of Psychology 3 (1910), 296-322; the reliability-of-a-sum form
used here is the standard parallel-model specialization. -/
theorem reliability_sum_spearmanBrown {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    {X : Fin k → Ω → ℝ} {T : Ω → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ j, X j = fun ω => T ω + E j ω)
    (hT : MemLp T 2 μ) (hE : ∀ j, MemLp (E j) 2 μ)
    (hTE : ∀ j, cov[T, E j; μ] = 0)
    (hEE : ∀ i j, i ≠ j → cov[E i, E j; μ] = 0)
    {v w : ℝ} (hv : 0 < v) (hw : 0 ≤ w)
    (hVarT : Var[T; μ] = v) (hVarE : ∀ j, Var[E j; μ] = w) :
    Var[fun ω => (k : ℝ) * T ω; μ] / Var[fun ω => ∑ j, X j ω; μ]
      = (k : ℝ) * attenuationFactor v w
        / (1 + ((k : ℝ) - 1) * attenuationFactor v w) := by
  have hnum : Var[fun ω => (k : ℝ) * T ω; μ] = (k : ℝ) ^ 2 * v := by
    rw [variance_const_mul, hVarT]
  let c0 : Fin k → ℝ := fun _ => 0
  have hX0 : ∀ j, X j = fun ω => T ω + c0 j + E j ω := by
    intro j
    rw [hX j]
    simp [c0]
  have hden := variance_sum_of_tauEquivalent μ hX0 hT hE hTE hEE
  rw [hVarT] at hden
  have hsumE : (∑ i, Var[E i; μ]) = (k : ℝ) * w := by
    have h1 : (∑ i, Var[E i; μ]) = ∑ i : Fin k, w := by
      apply Finset.sum_congr rfl
      intro j _
      exact hVarE j
    rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  rw [hsumE] at hden
  rw [hnum, hden]
  unfold attenuationFactor
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hkR
  have hvw : (0 : ℝ) < v + w := by linarith
  have hvw_ne : v + w ≠ 0 := ne_of_gt hvw
  have hdenL : (0:ℝ) < (k:ℝ)^2 * v + (k:ℝ) * w := by
    have hk2pos : (0:ℝ) < (k:ℝ)^2 := by positivity
    have h1 : (0:ℝ) < (k:ℝ)^2 * v := mul_pos hk2pos hv
    have h2 : (0:ℝ) ≤ (k:ℝ) * w := mul_nonneg (le_of_lt hkpos) hw
    linarith
  have hdenL_ne : (k:ℝ)^2 * v + (k:ℝ) * w ≠ 0 := ne_of_gt hdenL
  field_simp
  ring

end MathlibExt.Probability.Statistics.Measurement
