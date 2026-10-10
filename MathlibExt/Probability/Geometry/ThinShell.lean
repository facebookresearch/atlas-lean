/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Isotropic log-concave laws and thin-shell variance
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Probability.ThinShell

/-- A nonnegative Lebesgue density with concavity on every interior segment. -/
def IsLogConcaveDensity {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    ∀ x y : EuclideanSpace ℝ (Fin n), ∀ t : ℝ, 0 < t → t < 1 →
      Real.rpow (f x) (1 - t) * Real.rpow (f y) t ≤ f ((1 - t) • x + t • y)

/-- Actual probability, density and isotropic first/second moment conditions. -/
def IsIsotropicLogConcave {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsProbabilityMeasure μ ∧
    (∃ f : EuclideanSpace ℝ (Fin n) → ℝ, IsLogConcaveDensity f ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) ∧
    (∀ i : Fin n, Integrable (fun x => x i) μ ∧ (∫ x, x i ∂μ) = 0) ∧
    ∀ i j : Fin n, Integrable (fun x => x i * x j) μ ∧
      (∫ x, x i * x j ∂μ) = if i = j then 1 else 0

/-- Variance of the squared Euclidean radius, normalized by the dimension. -/
noncomputable def normalizedRadiusVariance {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal ((‖x‖ ^ 2 - (n : ℝ)) ^ 2) ∂μ) / (n : ℝ≥0∞)

/-- Optimal universal normalized variance over all positive dimensions and actual laws. -/
noncomputable def thinShellVarianceConstant : ℝ≥0∞ :=
  sSup {v | ∃ n : ℕ, 0 < n ∧ ∃ μ : Measure (EuclideanSpace ℝ (Fin n)),
    IsIsotropicLogConcave μ ∧ normalizedRadiusVariance μ = v}

/-- The dimension-specific thin-shell width of the Euclidean radius. -/
noncomputable def thinShellWidth (n : ℕ) : ℝ≥0∞ :=
  ENNReal.rpow (sSup {v | ∃ μ : Measure (EuclideanSpace ℝ (Fin n)),
    IsIsotropicLogConcave μ ∧
      (∫⁻ x, ENNReal.ofReal ((‖x‖ - Real.sqrt (n : ℝ)) ^ 2) ∂μ) = v}) (1 / 2)

/-- The pointwise radius fluctuation is bounded by the normalized squared-radius fluctuation. -/
theorem radius_deviation_sq_le {r d : ℝ} (hr : 0 ≤ r) (hd : 0 < d) :
    (r - Real.sqrt d) ^ 2 ≤ (r ^ 2 - d) ^ 2 / d := by
  have hs := Real.sqrt_nonneg d
  have hs2 := Real.sq_sqrt hd.le
  have hprod : 0 ≤ r * Real.sqrt d := by positivity
  have hsum : d ≤ (r + Real.sqrt d) ^ 2 := by nlinarith
  have hsq : 0 ≤ (r - Real.sqrt d) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hsq
  apply (le_div_iff₀ hd).2
  nlinarith [hmul]

/-- Integration preserves the radius-to-variance bound, even for infinite moments. -/
theorem radius_fluctuation_le_normalized_variance {n : ℕ} (hn : 0 < n)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    (∫⁻ x, ENNReal.ofReal ((‖x‖ - Real.sqrt (n : ℝ)) ^ 2) ∂μ) ≤
      normalizedRadiusVariance μ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hni : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    apply ENNReal.inv_ne_top.2
    exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (∫⁻ x, ENNReal.ofReal ((‖x‖ - Real.sqrt (n : ℝ)) ^ 2) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal ((‖x‖ ^ 2 - (n : ℝ)) ^ 2 / (n : ℝ)) ∂μ := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (radius_deviation_sq_le (norm_nonneg x) hnR)
    _ = (n : ℝ≥0∞)⁻¹ *
        (∫⁻ x, ENNReal.ofReal ((‖x‖ ^ 2 - (n : ℝ)) ^ 2) ∂μ) := by
      simp only [ENNReal.ofReal_div_of_pos hnR, ENNReal.ofReal_natCast]
      simpa only [div_eq_mul_inv, mul_comm] using
        lintegral_const_mul' (μ := μ) (n : ℝ≥0∞)⁻¹
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal ((‖x‖ ^ 2 - (n : ℝ)) ^ 2)) hni
    _ = normalizedRadiusVariance μ := by
      simp only [normalizedRadiusVariance, div_eq_mul_inv, mul_comm]

/-- Every admissible law contributes its actual variance to the universal supremum. -/
theorem normalizedRadiusVariance_le_constant {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    normalizedRadiusVariance μ ≤ thinShellVarianceConstant := by
  exact le_sSup ⟨n, hn, μ, hμ, rfl⟩

/-- The supremum is exactly the least simultaneous bound, not an unspecified oracle. -/
theorem thinShellVarianceConstant_le_iff {C : ℝ≥0∞} :
    thinShellVarianceConstant ≤ C ↔
      ∀ n : ℕ, 0 < n → ∀ μ : Measure (EuclideanSpace ℝ (Fin n)),
        IsIsotropicLogConcave μ → normalizedRadiusVariance μ ≤ C := by
  constructor
  · intro h n hn μ hμ
    exact (normalizedRadiusVariance_le_constant hn hμ).trans h
  · intro h
    apply sSup_le
    rintro v ⟨n, hn, μ, hμ, rfl⟩
    exact h n hn μ hμ

/-- The variance formulation controls the radius fluctuation for every actual law. -/
theorem radius_fluctuation_le_constant {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    (∫⁻ x, ENNReal.ofReal ((‖x‖ - Real.sqrt (n : ℝ)) ^ 2) ∂μ) ≤
      thinShellVarianceConstant := by
  exact (radius_fluctuation_le_normalized_variance hn μ).trans
    (normalizedRadiusVariance_le_constant hn hμ)

/-- The optimal variance constant is nonnegative in the extended nonnegative reals. -/
theorem thinShellVarianceConstant_nonneg : 0 ≤ thinShellVarianceConstant :=
  bot_le

/-- A variance bound gives a simultaneous dimension-independent bound on shell width. -/
theorem thinShellWidth_le_sqrt_constant {n : ℕ} (hn : 0 < n) :
    thinShellWidth n ≤ ENNReal.rpow thinShellVarianceConstant (1 / 2) := by
  unfold thinShellWidth
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply sSup_le
  rintro v ⟨μ, hμ, rfl⟩
  exact radius_fluctuation_le_constant hn hμ

/-- A finite simultaneous variance bound makes the optimal constant finite. -/
theorem thinShellVarianceConstant_lt_top_of_bound {C : ℝ}
    (hC : ∀ n : ℕ, 0 < n → ∀ μ : Measure (EuclideanSpace ℝ (Fin n)),
      IsIsotropicLogConcave μ → normalizedRadiusVariance μ ≤ ENNReal.ofReal C) :
    thinShellVarianceConstant < ⊤ := by
  exact lt_of_le_of_lt (thinShellVarianceConstant_le_iff.mpr hC) ENNReal.ofReal_lt_top

end MathlibExt.Probability.ThinShell
