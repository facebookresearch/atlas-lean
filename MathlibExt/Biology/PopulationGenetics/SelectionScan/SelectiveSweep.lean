/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp

/-!
# Selective sweeps: the logistic trajectory, sweep EHH and iHS

A favourable allele with genic selection coefficient `s > 0` follows, in the deterministic
(infinite-population) limit, the logistic equation `x' = s x (1 - x)`. `sweepTraj s x₀` is its
solution with `sweepTraj s x₀ 0 = x₀`, and `sweepDuration s a b` is the exact time the
trajectory takes from frequency `a` to frequency `b`.

The duration of a complete sweep in a population of `N` diploids, from one copy `1 / (2N)` to
`1 - 1 / (2N)`, is therefore `(2 / s) * log (2N - 1)` exactly. The frequently quoted
`(2 / s) * log (2Ns)` is a different quantity: the expected duration of a *stochastic* sweep
conditioned on establishment, which this file does not state.

Around a swept site, Voight et al. (2006) approximate the genealogy of the carriers by a star
with all `n` lineages coalescing at the start of the sweep, a time `T` ago, and declare two
carriers identical over a window of genetic length `d` exactly when neither of their two
lineages recombined out of the sweeping background. With recombination events falling on each
lineage as a Poisson process of rate `r * d` per unit time, the pair is identical with
probability `exp (-2 (r d) T)`: this is `sweepEhh r T d`. Integrating over the window length
gives the integrated haplotype homozygosity `ihh r T = (2 r T)⁻¹`, and the integrated
haplotype score `ihs r T_A T_D = log (ihh r T_A / ihh r T_D) = log (T_D / T_A)`, negative
exactly when the derived allele's star is the younger one.

All statements about `sweepEhh`, `ihh` and `ihs` are statements about this deterministic
star-genealogy model; they are not statements about expectations of the sample statistics
under the coalescent with recombination (in particular `ihs` is a log-ratio of model
quantities, not `E[log(iHH_A/iHH_D)]`).

## Main results

* `hasDerivAt_sweepTraj`, `sweepTraj_zero`, `sweepTraj_mem_Ioo`, `sweepTraj_strictMono`: the
  logistic trajectory solves `x' = s x (1 - x)`, starts at `x₀`, stays in `(0, 1)` and
  increases for `s > 0`.
* `sweepTraj_sweepDuration`, `sweepDuration_pos`: `sweepDuration s a b` is the exact time from
  `a` to `b`.
* `sweepDuration_full`: a complete sweep from `1 / (2N)` to `1 - 1 / (2N)` takes
  `(2 / s) * log (2N - 1)`.
* `sweepEhh_eq_poisson_sq`: the star-genealogy pair identity probability is the square of the
  probability that a Poisson count of mean `r d T` vanishes.
* `sweepEhh_antitone`, `tendsto_sweepEhh_atTop`: EHH decays in the window length.
* `ihh_eq`: `∫_0^∞ exp (-2 (r d) T) dd = (2 r T)⁻¹`.
* `ihs_eq_log_div`, `ihs_neg_iff`: `ihs = log (T_D / T_A)`, negative exactly when `T_D < T_A`.
* `sweepEhh_sweepDuration_full`: after a complete sweep, `EHH(d) = (2N - 1) ^ (-(4 r d / s))`.

## References

* J. Maynard Smith and J. Haigh, *The hitch-hiking effect of a favourable gene*,
  Genetical Research 23 (1974), 23–35.
* B. F. Voight, S. Kudaravalli, X. Wen and J. K. Pritchard, *A map of recent positive selection
  in the human genome*, PLoS Biology 4 (2006), e72.
-/

open MeasureTheory Set Real Filter Topology ProbabilityTheory

open scoped NNReal

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.SelectionScan

/-! ### The deterministic logistic sweep -/

/-- The logistic trajectory of a favourable allele with genic selection coefficient `s`,
starting from frequency `x₀`: the solution of `x' = s x (1 - x)` with `x 0 = x₀`
(Maynard Smith and Haigh 1974). -/
noncomputable def sweepTraj (s x₀ t : ℝ) : ℝ := x₀ * exp (s * t) / (1 - x₀ + x₀ * exp (s * t))

theorem sweepTraj_denom_pos {x₀ : ℝ} (h₀ : 0 < x₀) (h₁ : x₀ < 1) (s t : ℝ) :
    0 < 1 - x₀ + x₀ * exp (s * t) := by
  nlinarith [Real.exp_pos (s * t)]

@[simp] theorem sweepTraj_zero (s x₀ : ℝ) : sweepTraj s x₀ 0 = x₀ := by
  rw [sweepTraj, mul_zero, Real.exp_zero, mul_one,
    show 1 - x₀ + x₀ = 1 by ring, div_one]

/-- The trajectory stays strictly between `0` and `1`. -/
theorem sweepTraj_mem_Ioo {x₀ : ℝ} (h₀ : 0 < x₀) (h₁ : x₀ < 1) (s t : ℝ) :
    sweepTraj s x₀ t ∈ Ioo (0 : ℝ) 1 := by
  have hden := sweepTraj_denom_pos h₀ h₁ s t
  have he := Real.exp_pos (s * t)
  constructor
  · exact div_pos (by positivity) hden
  · rw [sweepTraj, div_lt_one hden]
    linarith

/-- The logistic equation: `x'(t) = s x(t) (1 - x(t))`. -/
theorem hasDerivAt_sweepTraj {x₀ : ℝ} (h₀ : 0 < x₀) (h₁ : x₀ < 1) (s t : ℝ) :
    HasDerivAt (sweepTraj s x₀) (s * sweepTraj s x₀ t * (1 - sweepTraj s x₀ t)) t := by
  have hden := sweepTraj_denom_pos h₀ h₁ s t
  have hlin : HasDerivAt (fun u : ℝ => s * u) s t := by
    simpa using (hasDerivAt_id t).const_mul s
  have he : HasDerivAt (fun u : ℝ => exp (s * u)) (exp (s * t) * s) t := hlin.exp
  have hnum : HasDerivAt (fun u : ℝ => x₀ * exp (s * u)) (x₀ * (exp (s * t) * s)) t :=
    he.const_mul x₀
  have hden' : HasDerivAt (fun u : ℝ => 1 - x₀ + x₀ * exp (s * u))
      (x₀ * (exp (s * t) * s)) t := hnum.const_add _
  have h := hnum.div hden' hden.ne'
  convert h using 1
  · funext u
    simp [sweepTraj, Pi.div_apply]
  · simp only [sweepTraj]
    field_simp

theorem sweepTraj_strictMono {s x₀ : ℝ} (hs : 0 < s) (h₀ : 0 < x₀) (h₁ : x₀ < 1) :
    StrictMono (sweepTraj s x₀) := by
  intro a b hab
  have hda := sweepTraj_denom_pos h₀ h₁ s a
  have hdb := sweepTraj_denom_pos h₀ h₁ s b
  have hexp : exp (s * a) < exp (s * b) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  rw [sweepTraj, sweepTraj, div_lt_div_iff₀ hda hdb]
  nlinarith [mul_pos h₀ (sub_pos.mpr h₁), Real.exp_pos (s * a), Real.exp_pos (s * b)]

/-- The time the logistic trajectory with selection coefficient `s` takes to go from frequency
`a` to frequency `b`: `(1/s) log (b (1 - a) / (a (1 - b)))`, the difference of the logits
divided by `s`. -/
noncomputable def sweepDuration (s a b : ℝ) : ℝ := (1 / s) * log (b * (1 - a) / (a * (1 - b)))

/-- `sweepDuration s a b` is the exact time at which the trajectory started at `a` reaches
`b`. -/
theorem sweepTraj_sweepDuration {s a b : ℝ} (hs : s ≠ 0) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) : sweepTraj s a (sweepDuration s a b) = b := by
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  have hx : 0 < b * (1 - a) / (a * (1 - b)) := by positivity
  rw [sweepTraj, sweepDuration, show s * (1 / s * log (b * (1 - a) / (a * (1 - b))))
      = log (b * (1 - a) / (a * (1 - b))) by field_simp, Real.exp_log hx]
  field_simp
  ring

/-- The time to reach a higher frequency is positive. -/
theorem sweepDuration_pos {s a b : ℝ} (hs : 0 < s) (ha₀ : 0 < a) (hab : a < b) (hb₁ : b < 1) :
    0 < sweepDuration s a b := by
  have h1b : 0 < 1 - b := by linarith
  have h1a : 0 < 1 - a := by linarith
  have harg : 1 < b * (1 - a) / (a * (1 - b)) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hlog := Real.log_pos harg
  have hs' : 0 < 1 / s := by positivity
  exact mul_pos hs' hlog

/-- A complete sweep in a population of `N` diploids, from a single copy `1 / (2N)` to
`1 - 1 / (2N)`, takes exactly `(2 / s) log (2N - 1)` generations in the deterministic logistic
model. (The familiar `(2 / s) log (2Ns)` is the conditional expected duration of the
corresponding stochastic sweep, a different quantity.) -/
theorem sweepDuration_full {s N : ℝ} (hs : s ≠ 0) (hN : 1 < N) :
    sweepDuration s (1 / (2 * N)) (1 - 1 / (2 * N)) = (2 / s) * log (2 * N - 1) := by
  have h2N : (0 : ℝ) < 2 * N := by linarith
  have hN2 : (0 : ℝ) < 2 * N - 1 := by linarith
  have harg : (1 - 1 / (2 * N)) * (1 - 1 / (2 * N)) /
      (1 / (2 * N) * (1 - (1 - 1 / (2 * N)))) = (2 * N - 1) ^ 2 := by
    field_simp
    ring
  rw [sweepDuration, harg, Real.log_pow]
  push_cast
  field_simp

/-! ### Extended haplotype homozygosity under a star-shaped sweep genealogy -/

/-- The probability that two carriers of a swept allele are identical over a window of genetic
length `d`, in the star-genealogy model of Voight et al. (2006): all carriers coalesce at the
start of the sweep, a time `T` ago, and the pair is identical exactly when neither of its two
lineages recombined, each at rate `r * d` per unit time. -/
noncomputable def sweepEhh (r T d : ℝ) : ℝ := exp (-2 * (r * d) * T)

/-- The star-genealogy EHH is the square of the probability that a Poisson number of
recombination events with mean `r d T` on one lineage is zero. -/
theorem sweepEhh_eq_poisson_sq (r T d : ℝ≥0) :
    sweepEhh r T d = ((poissonMeasure (r * d * T)).real {0}) ^ 2 := by
  rw [sweepEhh, poissonMeasure_real_singleton]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, sq, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem sweepEhh_pos (r T d : ℝ) : 0 < sweepEhh r T d := exp_pos _

theorem sweepEhh_le_one {r T d : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hd : 0 ≤ d) :
    sweepEhh r T d ≤ 1 := by
  rw [sweepEhh, exp_le_one_iff]
  nlinarith [mul_nonneg (mul_nonneg hr hd) hT]

@[simp] theorem sweepEhh_zero (r T : ℝ) : sweepEhh r T 0 = 1 := by
  simp [sweepEhh]

/-- Haplotype homozygosity decays with the window length. -/
theorem sweepEhh_antitone {r T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) {d d' : ℝ} (hd : d ≤ d') :
    sweepEhh r T d' ≤ sweepEhh r T d := by
  rw [sweepEhh, sweepEhh, exp_le_exp]
  nlinarith [mul_nonneg (mul_nonneg hr hT) (sub_nonneg.mpr hd)]

theorem tendsto_sweepEhh_atTop {r T : ℝ} (hr : 0 < r) (hT : 0 < T) :
    Tendsto (sweepEhh r T) atTop (𝓝 0) := by
  have hb : (0 : ℝ) < 2 * r * T := by positivity
  have h1 : Tendsto (fun d : ℝ => 2 * r * T * d) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hb tendsto_id
  have hlin : Tendsto (fun d : ℝ => -(2 * r * T * d)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  have h2 : Tendsto (fun d : ℝ => exp (-(2 * r * T * d))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  refine h2.congr fun d => ?_
  rw [sweepEhh]
  congr 1
  ring

/-- The integrated haplotype homozygosity: the area under the EHH decay curve. -/
noncomputable def ihh (r T : ℝ) : ℝ := ∫ d in Ioi (0 : ℝ), sweepEhh r T d

/-- In the star-genealogy model the integrated haplotype homozygosity is `1 / (2 r T)`. -/
theorem ihh_eq {r T : ℝ} (hr : 0 < r) (hT : 0 < T) : ihh r T = (2 * r * T)⁻¹ := by
  have hb : (0 : ℝ) < 2 * r * T := by positivity
  have hcongr : ∀ d ∈ Ioi (0 : ℝ), sweepEhh r T d = (fun y : ℝ => exp (-y)) ((2 * r * T) * d) := by
    intro d _
    rw [sweepEhh]
    ring_nf
  rw [ihh, setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_comp_mul_left_Ioi (fun y : ℝ => exp (-y)) 0 hb, mul_zero,
    integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one]

theorem ihh_pos {r T : ℝ} (hr : 0 < r) (hT : 0 < T) : 0 < ihh r T := by
  rw [ihh_eq hr hT]
  positivity

/-- The integrated haplotype score of Voight et al. (2006): the log ratio of the integrated
haplotype homozygosities of the ancestral and the derived allele, whose star genealogies have
ages `T_A` and `T_D`. -/
noncomputable def ihs (r T_A T_D : ℝ) : ℝ := log (ihh r T_A / ihh r T_D)

/-- In the star-genealogy model the integrated haplotype score is the log ratio of the two
ages, so the recombination rate cancels. -/
theorem ihs_eq_log_div {r T_A T_D : ℝ} (hr : 0 < r) (hA : 0 < T_A) (hD : 0 < T_D) :
    ihs r T_A T_D = log (T_D / T_A) := by
  rw [ihs, ihh_eq hr hA, ihh_eq hr hD]
  congr 1
  field_simp

/-- The integrated haplotype score is negative exactly when the derived allele's star
genealogy is the younger one, i.e. when the derived allele swept faster. -/
theorem ihs_neg_iff {r T_A T_D : ℝ} (hr : 0 < r) (hA : 0 < T_A) (hD : 0 < T_D) :
    ihs r T_A T_D < 0 ↔ T_D < T_A := by
  rw [ihs_eq_log_div hr hA hD, Real.log_neg_iff (by positivity)]
  rw [div_lt_one hA]

/-- Combining the exact sweep duration with the star-genealogy decay: after a complete sweep
of a favourable allele with selection coefficient `s` in a population of `N` diploids, the
extended haplotype homozygosity at genetic distance `d` is the power law
`(2N - 1) ^ (-(4 r d / s))`. -/
theorem sweepEhh_sweepDuration_full {r s N d : ℝ} (hs : 0 < s) (hN : 1 < N) :
    sweepEhh r (sweepDuration s (1 / (2 * N)) (1 - 1 / (2 * N))) d
      = (2 * N - 1) ^ (-(4 * r * d / s)) := by
  have hN2 : (0 : ℝ) < 2 * N - 1 := by linarith
  rw [sweepDuration_full hs.ne' hN, sweepEhh, Real.rpow_def_of_pos hN2]
  congr 1
  field_simp
  ring

end MathlibExt.Biology.PopulationGenetics.SelectionScan
