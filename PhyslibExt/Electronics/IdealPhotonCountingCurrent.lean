/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Variance
public import MathlibExt.Probability.Distributions.PoissonKernel

/-!
# Ideal photon-counting detector current

## i. Overview

An ideal photodetector with quantum efficiency `η`, optical power
`P`, photon energy `hν` and charge `q` counts photons in a window
of length `T`. The count is Poisson with mean rate
`ηP/(hν)`, the window-averaged current is `|q| n / T`, and the
detector responsivity is `η|q|/(hν)`. The mean current is
responsivity times power, and its variance is
`q² λ / T`. The Poisson mean and variance facts are the canonical
MathlibExt results `ProbabilityTheory.integral_natCast_poissonMeasure`
and `ProbabilityTheory.variance_natCast_poissonMeasure`; private
`_of_poisson...` variants take them as explicit hypotheses and the
public lemmas discharge them.

## ii. Key results

- `integral_countCurrent_eq_responsivity_mul_power`: the mean
  window-averaged current equals responsivity times power.
- `variance_countCurrent_eq_sq_charge_mul_rate_div`: the current
  variance is `q² λ / T`.
- `countCurrent_moments_eq_zero_of_efficiency_zero` and the
  zero-power case: a detector that counts nothing has zero mean
  and zero variance. (The negative-power diagnostic lives in the
  test module, not the public API.)
- `variance_countCurrent_double_window`: doubling the window
  halves the variance.

## iii. Table of contents

- A. Moments of the ideal detector current

## iv. References

- B. P. Lathi and Z. Ding, *Modern Digital and Analog Communication
Systems*, fifth edition, Oxford University Press, 2019: photodetection, Poisson counting noise and
  responsivity.

## A. Moments of the ideal detector current
-/

@[expose] public section

namespace PhyslibExt.Electronics.IdealPhotonCountingCurrent

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Mean photon-electron arrival rate `λ = η P / (h ν)` of an ideal detector with quantum
efficiency `η`, optical power `P` and photon energy `h ν`. -/
noncomputable def photonArrivalRate (η P h ν : ℝ) : ℝ :=
  η * P / (h * ν)

/-- Ideal responsivity `R = η |q| / (h ν)` (current per unit optical power). -/
noncomputable def responsivity (η q h ν : ℝ) : ℝ :=
  η * |q| / (h * ν)

/-- Poisson mean `λ T` of the count in a window of length `T`, as a nonnegative real. It is that
mean for physical inputs (nonnegative efficiency and power, positive `h`, `ν` and window length;
`coe_photonCountMean`); a negative raw product `λ T` from unphysical inputs is clamped to `0` by
`toNNReal`. -/
noncomputable def photonCountMean (η P h ν T : ℝ) : ℝ≥0 :=
  (photonArrivalRate η P h ν * T).toNNReal

/-- Window-averaged current estimator `|q| n / T` for `n` counted electrons, a window average for
a window of positive length `T > 0`. For `T = 0` the value is `0` (`x / 0 = 0`), not a current. -/
noncomputable def countCurrent (q T : ℝ) (n : ℕ) : ℝ :=
  |q| * (n : ℝ) / T

/-- Under the leaf hypotheses the nonnegative Poisson mean is exactly `λ T`. -/
lemma coe_photonCountMean (η P h ν T : ℝ) (hη0 : 0 ≤ η) (hP : 0 ≤ P) (hh : 0 < h)
    (hν : 0 < ν) (hT : 0 < T) :
    ((photonCountMean η P h ν T : ℝ≥0) : ℝ) = photonArrivalRate η P h ν * T := by
  unfold photonCountMean
  rw [Real.coe_toNNReal]
  unfold photonArrivalRate
  positivity

/-- `R P = |q| λ`: responsivity times power is the charge flux. -/
lemma responsivity_mul_power_eq (η P q h ν : ℝ) :
    responsivity η q h ν * P = |q| * photonArrivalRate η P h ν := by
  unfold responsivity photonArrivalRate
  ring

/-- **Mean detector current.** For `N_T ∼ Poisson(λ T)`, `E[|q| N_T / T] = R P`. -/
private lemma integral_countCurrent_eq_responsivity_mul_power_of_poissonMean (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (η P h ν q T : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hP : 0 ≤ P) (hh : 0 < h) (hν : 0 < ν) (hq : q ≠ 0) (hT : 0 < T)
    (hN : HasLaw N (poissonMeasure (photonCountMean η P h ν T)) μ)
    (hPoissonMean : ∀ r : ℝ≥0, ∫ n, (n : ℝ) ∂(poissonMeasure r) = r) :
    ∫ ω, countCurrent q T (N ω) ∂μ = responsivity η q h ν * P := by
  have hmeas : AEStronglyMeasurable (fun n : ℕ => countCurrent q T n)
      (poissonMeasure (photonCountMean η P h ν T)) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hcomp := hN.integral_comp hmeas
  simp only [Function.comp_apply] at hcomp
  rw [hcomp]
  unfold countCurrent
  rw [integral_div, integral_const_mul]
  rw [hPoissonMean]
  rw [coe_photonCountMean η P h ν T hη0 hP hh hν hT]
  rw [responsivity_mul_power_eq]
  have hTne : T ≠ 0 := ne_of_gt hT
  field_simp

/-- **Detector current count noise.** For `N_T ∼ Poisson(λ T)`,
`Var(|q| N_T / T) = q² λ / T`. -/
private lemma variance_countCurrent_eq_sq_charge_mul_rate_div_of_poissonVar (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (η P h ν q T : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hP : 0 ≤ P) (hh : 0 < h) (hν : 0 < ν) (hq : q ≠ 0) (hT : 0 < T)
    (hN : HasLaw N (poissonMeasure (photonCountMean η P h ν T)) μ)
    (hPoissonVar : ∀ r : ℝ≥0, Var[fun n : ℕ => (n : ℝ); poissonMeasure r] = r) :
    Var[fun ω => countCurrent q T (N ω); μ] = q ^ 2 * photonArrivalRate η P h ν / T := by
  have hmeas_g : AEMeasurable (fun n : ℕ => countCurrent q T n) (μ.map N) :=
    (measurable_of_countable _).aemeasurable
  have hvar_transfer := variance_map hmeas_g hN.aemeasurable
  rw [hN.map_eq] at hvar_transfer
  have hcomp_eq : (fun ω => countCurrent q T (N ω))
      = ((fun n : ℕ => countCurrent q T n) ∘ N) := rfl
  rw [hcomp_eq, ← hvar_transfer]
  have hg : (fun n : ℕ => countCurrent q T n)
      = (fun n : ℕ => (|q| / T) * (n : ℝ)) := by
    funext n
    unfold countCurrent
    ring
  rw [hg, variance_const_mul, hPoissonVar]
  rw [coe_photonCountMean η P h ν T hη0 hP hh hν hT]
  have hTne : T ≠ 0 := ne_of_gt hT
  have hsq : |q| ^ 2 = q ^ 2 := sq_abs q
  rw [div_pow, hsq]
  field_simp

/-- Validation, `η = 0`: zero mean current and zero variance. -/
private lemma countCurrent_moments_eq_zero_of_efficiency_zero_of_poisson_moments (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (P h ν q T : ℝ) (hP : 0 ≤ P) (hh : 0 < h) (hν : 0 < ν)
    (hq : q ≠ 0) (hT : 0 < T)
    (hN : HasLaw N (poissonMeasure (photonCountMean 0 P h ν T)) μ)
    (hPoissonMean : ∀ r : ℝ≥0, ∫ n, (n : ℝ) ∂(poissonMeasure r) = r)
    (hPoissonVar : ∀ r : ℝ≥0, Var[fun n : ℕ => (n : ℝ); poissonMeasure r] = r) :
    ∫ ω, countCurrent q T (N ω) ∂μ = 0 ∧ Var[fun ω => countCurrent q T (N ω); μ] = 0 := by
  have hmean := integral_countCurrent_eq_responsivity_mul_power_of_poissonMean Ω μ N 0 P h ν q T
    (le_refl 0) zero_le_one hP hh hν hq hT hN hPoissonMean
  have hvar := variance_countCurrent_eq_sq_charge_mul_rate_div_of_poissonVar Ω μ N 0 P h ν q T
    (le_refl 0) zero_le_one hP hh hν hq hT hN hPoissonVar
  have hR : responsivity 0 q h ν = 0 := by unfold responsivity; simp
  have hL : photonArrivalRate 0 P h ν = 0 := by unfold photonArrivalRate; simp
  rw [hR, zero_mul] at hmean
  rw [hL, mul_zero, zero_div] at hvar
  exact ⟨hmean, hvar⟩

/-- Validation, `P = 0`: zero mean current and zero variance. -/
private lemma countCurrent_moments_eq_zero_of_power_zero_of_poisson_moments (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (η h ν q T : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hh : 0 < h)
    (hν : 0 < ν) (hq : q ≠ 0) (hT : 0 < T)
    (hN : HasLaw N (poissonMeasure (photonCountMean η 0 h ν T)) μ)
    (hPoissonMean : ∀ r : ℝ≥0, ∫ n, (n : ℝ) ∂(poissonMeasure r) = r)
    (hPoissonVar : ∀ r : ℝ≥0, Var[fun n : ℕ => (n : ℝ); poissonMeasure r] = r) :
    ∫ ω, countCurrent q T (N ω) ∂μ = 0 ∧ Var[fun ω => countCurrent q T (N ω); μ] = 0 := by
  have hmean := integral_countCurrent_eq_responsivity_mul_power_of_poissonMean Ω μ N η 0 h ν q T
    hη0 hη1 (le_refl 0) hh hν hq hT hN hPoissonMean
  have hvar := variance_countCurrent_eq_sq_charge_mul_rate_div_of_poissonVar Ω μ N η 0 h ν q T
    hη0 hη1 (le_refl 0) hh hν hq hT hN hPoissonVar
  have hL : photonArrivalRate η 0 h ν = 0 := by unfold photonArrivalRate; simp
  rw [hL, mul_zero, zero_div] at hvar
  rw [mul_zero] at hmean
  exact ⟨hmean, hvar⟩

/-- Validation, doubling the window at fixed `λ`: if `N₂ ∼ Poisson(λ · 2T)` and
`N₁ ∼ Poisson(λ T)`, the `2T`-window current variance is half the `T`-window one. -/
private lemma variance_countCurrent_double_window_of_poissonVar (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (N₁ N₂ : Ω → ℕ) (η P h ν q T : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hP : 0 ≤ P) (hh : 0 < h) (hν : 0 < ν) (hq : q ≠ 0) (hT : 0 < T)
    (hN₁ : HasLaw N₁ (poissonMeasure (photonCountMean η P h ν T)) μ)
    (hN₂ : HasLaw N₂ (poissonMeasure (photonCountMean η P h ν (2 * T))) μ)
    (hPoissonVar : ∀ r : ℝ≥0, Var[fun n : ℕ => (n : ℝ); poissonMeasure r] = r) :
    Var[fun ω => countCurrent q (2 * T) (N₂ ω); μ] =
      Var[fun ω => countCurrent q T (N₁ ω); μ] / 2 := by
  have h1 := variance_countCurrent_eq_sq_charge_mul_rate_div_of_poissonVar Ω μ N₁ η P h ν q T
    hη0 hη1 hP hh hν hq hT hN₁ hPoissonVar
  have hT2 : 0 < 2 * T := by linarith
  have h2 := variance_countCurrent_eq_sq_charge_mul_rate_div_of_poissonVar Ω μ N₂ η P h ν q (2 * T)
    hη0 hη1 hP hh hν hq hT2 hN₂ hPoissonVar
  rw [h1, h2]
  have hTne : T ≠ 0 := ne_of_gt hT
  field_simp

/-- **Mean detector current, Poisson mean discharged.** As
`integral_countCurrent_eq_responsivity_mul_power_of_poissonMean`, with
the Poisson mean supplied by the canonical
`ProbabilityTheory.integral_natCast_poissonMeasure`. -/
lemma integral_countCurrent_eq_responsivity_mul_power (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (η P h ν q T : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hP : 0 ≤ P) (hh : 0 < h) (hν : 0 < ν) (hq : q ≠ 0) (hT : 0 < T)
    (hN : HasLaw N (poissonMeasure (photonCountMean η P h ν T)) μ) :
    ∫ ω, countCurrent q T (N ω) ∂μ = responsivity η q h ν * P :=
  integral_countCurrent_eq_responsivity_mul_power_of_poissonMean Ω μ N η P h ν q T
    hη0 hη1 hP hh hν hq hT hN
    (fun r => ProbabilityTheory.integral_natCast_poissonMeasure r)

/-- **Current variance, Poisson variance discharged.** As
`variance_countCurrent_eq_sq_charge_mul_rate_div_of_poissonVar`, with
the Poisson variance supplied by the canonical
`ProbabilityTheory.variance_natCast_poissonMeasure`. -/
lemma variance_countCurrent_eq_sq_charge_mul_rate_div (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (η P h ν q T : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hP : 0 ≤ P) (hh : 0 < h) (hν : 0 < ν) (hq : q ≠ 0) (hT : 0 < T)
    (hN : HasLaw N (poissonMeasure (photonCountMean η P h ν T)) μ) :
    Var[fun ω => countCurrent q T (N ω); μ] = q ^ 2 * photonArrivalRate η P h ν / T :=
  variance_countCurrent_eq_sq_charge_mul_rate_div_of_poissonVar Ω μ N η P h ν q T
    hη0 hη1 hP hh hν hq hT hN
    (fun r => ProbabilityTheory.variance_natCast_poissonMeasure r)

/-- **Zero-efficiency moments, discharged.** With `η = 0` the detector
counts nothing: mean and variance are zero. Poisson facts are the
canonical `ProbabilityTheory.integral_natCast_poissonMeasure` and
`ProbabilityTheory.variance_natCast_poissonMeasure`. -/
lemma countCurrent_moments_eq_zero_of_efficiency_zero (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (P h ν q T : ℝ) (hP : 0 ≤ P) (hh : 0 < h) (hν : 0 < ν)
    (hq : q ≠ 0) (hT : 0 < T)
    (hN : HasLaw N (poissonMeasure (photonCountMean 0 P h ν T)) μ) :
    ∫ ω, countCurrent q T (N ω) ∂μ = 0 ∧ Var[fun ω => countCurrent q T (N ω); μ] = 0 :=
  countCurrent_moments_eq_zero_of_efficiency_zero_of_poisson_moments Ω μ N P h ν q T
    hP hh hν hq hT hN
    (fun r => ProbabilityTheory.integral_natCast_poissonMeasure r)
    (fun r => ProbabilityTheory.variance_natCast_poissonMeasure r)

/-- **Zero-power moments, discharged.** With `P = 0` the detector
counts nothing: mean and variance are zero. -/
lemma countCurrent_moments_eq_zero_of_power_zero (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (η h ν q T : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hh : 0 < h)
    (hν : 0 < ν) (hq : q ≠ 0) (hT : 0 < T)
    (hN : HasLaw N (poissonMeasure (photonCountMean η 0 h ν T)) μ) :
    ∫ ω, countCurrent q T (N ω) ∂μ = 0 ∧ Var[fun ω => countCurrent q T (N ω); μ] = 0 :=
  countCurrent_moments_eq_zero_of_power_zero_of_poisson_moments Ω μ N η h ν q T
    hη0 hη1 hh hν hq hT hN
    (fun r => ProbabilityTheory.integral_natCast_poissonMeasure r)
    (fun r => ProbabilityTheory.variance_natCast_poissonMeasure r)

/-- **Doubling the window halves the variance, discharged.** -/
lemma variance_countCurrent_double_window (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (N₁ N₂ : Ω → ℕ) (η P h ν q T : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hP : 0 ≤ P) (hh : 0 < h) (hν : 0 < ν) (hq : q ≠ 0) (hT : 0 < T)
    (hN₁ : HasLaw N₁ (poissonMeasure (photonCountMean η P h ν T)) μ)
    (hN₂ : HasLaw N₂ (poissonMeasure (photonCountMean η P h ν (2 * T))) μ) :
    Var[fun ω => countCurrent q (2 * T) (N₂ ω); μ] =
      Var[fun ω => countCurrent q T (N₁ ω); μ] / 2 :=
  variance_countCurrent_double_window_of_poissonVar Ω μ N₁ N₂ η P h ν q T
    hη0 hη1 hP hh hν hq hT hN₁ hN₂
    (fun r => ProbabilityTheory.variance_natCast_poissonMeasure r)

end PhyslibExt.Electronics.IdealPhotonCountingCurrent
