/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.KMRemainder
public import MathlibExt.Probability.Statistics.Survival.CountingProcess
public import Mathlib.Probability.Distributions.Exponential

/-!
# The Kaplan–Meier remainder in continuous time

Gill's representation of the Kaplan–Meier estimator in continuous time, for one subject with
latent failure time `T` and censoring time `C` on the time axis `ℝ` (the model of
`MathlibExt/Probability/Statistics/Survival/CountingProcess.lean`), and nonzero examples. The
discrete-grid version (time `0, 1, 2, …`) is `KMRemainder.lean`.

## The representation

Let `S` be a survival function and `Λ` a hazard measure on `ℝ`, linked by the **Volterra
identity** `1/S(b) - 1/S(a) = ∫_{(a, b]} dΛ/S` for `0 ≤ a ≤ b ≤ t`, with `S(0) = 1`.
The product integral `S = ∏_{(0, ·]} (1 - dΛ)` of a locally finite `Λ` with atoms `< 1` satisfies
it, atoms included (at an atom, `1/S(s) - 1/S(s-) = ΔΛ(s)/S(s)` is `S(s) = S(s-)(1 - ΔΛ(s))`).
On its own the identity does not pin down `S`: the integral is a Bochner integral, which is `0`
for a non-integrable integrand, so `S ≡ 1` with a `Λ` of infinite mass on every interval also
satisfies it. The representation is a pathwise identity and holds under the Volterra identity
alone; the mean-bias theorem adds `1/S` integrable on `(0, t]`, `S` nonincreasing and `S(t) > 0`.
Mathlib has no Lebesgue–Stieltjes product integral (its construction is the unmerged task T77),
so it enters as an explicit hypothesis. This follows the policy of
`MathlibExt/Probability/Statistics/ContinuousProductIntegral.lean`, but the hypothesis differs:
that file assumes a Duhamel-equation predicate (`IsDuhamelProductIntegral`) on the
product-integral map, while here one fixed `S` is tied to `Λ` by the Volterra identity.

With `Ŝ` the Kaplan–Meier estimator (`kaplanMeierOne`, the grouped-data
`CensoredData.kmSurvival` of the one-subject sample, `= 1 - N`), `N` the counting process, `Y` the
at-risk process and `A = ∫ Y dΛ` the compensator, `kaplanMeierOne_div_sub_one` proves, for a
subject at risk at time `0`,

`Ŝ(t)/S(t) - 1 = -∫_{(0, t]} Ŝ(s-) / (S(s) Y(s)) d(N - A)(s) + R(t)`,
`R(t) = ∫_{(0, t]} Ŝ(s-)/S(s) · 1{Y(s) = 0} dΛ(s)` (`kmRemainder`).

`dN` is the measure `countingMeasure` (a unit mass at an observed failure), `Ŝ(s-)` is the left
limit `kaplanMeierOneLeft` (`tendsto_kaplanMeierOne_left`), and `x / 0 = 0` plays the role of
Gill's indicator `J = 1{Y > 0}`.

## When the remainder vanishes, and when it does not

* `kmRemainder_eq`: `R(t) = 1{C < T, C ≤ t} (1/S(t) - 1/S(C))`.
* `kmRemainder_eq_zero_of_le`: **no censoring, no remainder** (`T ≤ C`), for every `S`, `Λ`;
  `kmRemainder_eq_zero_of_le_obsTime`: `R(t) = 0` while the subject is at risk (`t ≤ X`).
* `kmRemainder_nonneg`, `kmRemainder_pos`: `R ≥ 0` for nonincreasing positive `S`, and `R(t) > 0`
  after censoring at `C ≤ t` if `S(t) < S(C)` (which forces `C ≠ t`).
* `integral_kaplanMeierOne_div_sub_one`: **the mean bias is the mean remainder**,
  `E[Ŝ(t)/S(t) - 1] = E[R(t)]`, under independent censoring with `Λ` the hazard measure of the
  law of `T`. The martingale term has mean zero by the weighted compensator identity
  `lintegral_setLIntegral_Iic_obsTime` (`E ∫ g Y dΛ = E ∫ g dN` for measurable `g ≥ 0`), which
  extends `lintegral_hazardMeasure_inter_Iic_obsTime` from indicators to weights.
* **Exponential failure, censoring at time `1`** (`ExpCensoredAtOne`): `T ~ Exp(1)`, `C ≡ 1`,
  `S(t) = e^{-t}` (`measureReal_Ioi`), and `Λ = hazardMeasure (Exp(1))` is Lebesgue measure on
  `(0, ∞)` (`hazardMeasure_restrict_Ioi`), so the Volterra hypothesis holds (`volterra_hazard`).
  For `t ≥ 1`, `R(t) = 1{T > 1} (e^t - e)` (`kmRemainder_eq_indicator`) is known at time `1`, and
  `E[R(t) | ℱ₁] = R(t)` (`condExp_kmRemainder`) is not a.e. zero for `t > 1`
  (`condExp_kmRemainder_ne_zero`), with `ℱ` the history filtration `historyFiltration`. The mean
  bias is `E[Ŝ(t)/S(t)] - 1 = E[R(t)] = e^{t-1} - 1`
  (`integral_kaplanMeierOne_div_sub_one_eq_integral_kmRemainder`, `integral_kmRemainder`), both
  sides computed independently of the general theorem.

## Scope

* **One subject.** Gill's theorem is for `n` subjects. The `n`-subject model exists
  (`totalCountingProcess`, `totalAtRiskProcess` in `CountingProcess.lean`); what is missing is an
  `n`-subject continuous-time Kaplan–Meier definition on it. With `n` subjects `Ŝ` has finitely
  many jumps, so the identity is a finite telescoping sum over the ordered observation times,
  using the Volterra identity on each gap. That is left to a follow-up. The `n`-subject
  discrete-grid version is `kaplanMeierProcess_div_sub_one`.
* **The product integral is a hypothesis** (the Volterra identity above), not constructed.

## Source receipt (reuse search, 2026-11-12)

Mathlib v4.35.0 has no product integral and no continuous-time Kaplan–Meier estimator. Reused:
`obsTime`, `countingProcess`, `censoringProcess`, `atRiskProcess`, `atRiskProcess_eq_indicator`,
`hazardMeasure`, `measurable_measure_Ici`, `lintegral_hazardMeasure_inter_Iic_obsTime`,
`measurable_countingProcess`, `countingProcess_mem`, `historyFiltration`,
`measurable_observedProcess_history` (`CountingProcess.lean`); `CensoredData`,
`CensoredData.kmSurvival` (`KaplanMeier.lean`, reached through the `KMRemainder.lean` import);
`ProbabilityTheory.expMeasure`, `cdf_expMeasure_eq`, `exponentialPDF_of_nonneg`, `integral_exp`,
`withDensity_mul`, `restrict_withDensity`, `lintegral_lintegral_swap`,
`lintegral_withDensity_eq_lintegral_mul`, `integral_toReal`, `condExp_of_stronglyMeasurable`
(Mathlib). The discrete statements of `KMRemainder.lean` are the time-discrete counterparts.

## References

* R. D. Gill, *Censoring and Stochastic Integrals*, Mathematical Centre Tracts 124, Amsterdam
  (1980), Theorem 3.2.1 (the representation of `Ŝ/S - 1` with the vanishing-risk remainder) and
  Section 3.2.
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Section IV.3.1.
* R. D. Gill and S. Johansen, *A survey of product-integration with a view toward application in
  survival analysis*, Ann. Statist. 18 (1990), 1501–1555 (the Volterra/Duhamel identities).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MathlibExt.Probability.Statistics.KaplanMeier

variable {Ω : Type*} {T C : Ω → ℝ}

/-! ### The one-subject Kaplan–Meier estimator in continuous time -/

/-- The grouped censored data of one subject: a single observation time `X(ω) = T ∧ C`, with an
event iff `T ≤ C`. -/
noncomputable def oneSubjectData (T C : Ω → ℝ) (ω : Ω) : CensoredData 1 where
  time _ := obsTime T C ω
  strictMono_time := Subsingleton.strictMono _
  deaths _ := if T ω ≤ C ω then 1 else 0
  censored _ := if T ω ≤ C ω then 0 else 1

/-- The **Kaplan–Meier estimator of one subject** in continuous time,
`Ŝ(t) = ∏_{s ≤ t} (1 - ΔN(s) / Y(s))`: the grouped-data estimator `CensoredData.kmSurvival` of the
one-subject sample. -/
noncomputable def kaplanMeierOne (T C : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (oneSubjectData T C ω).kmSurvival t

/-- `Ŝ(t) = 1 - N(t)`: the estimator drops from `1` to `0` at an observed failure. -/
theorem kaplanMeierOne_eq (t : ℝ) (ω : Ω) :
    kaplanMeierOne T C t ω = 1 - countingProcess T C t ω := by
  simp only [kaplanMeierOne, CensoredData.kmSurvival, oneSubjectData, CensoredData.kmFactor,
    CensoredData.atRisk, countingProcess]
  by_cases hTC : T ω ≤ C ω
  · by_cases hT : T ω ≤ t
    · have hX : obsTime T C ω ≤ t := (min_le_left _ _).trans hT
      simp [hTC, hT, obsTime, Finset.filter_true_of_mem]
    · have hX : ¬ obsTime T C ω ≤ t := by simp [obsTime, min_eq_left hTC, hT]
      simp [hTC, hT, hX]
  · simp [hTC]

/-- The left limit `Ŝ(t-) = 1 - N(t-) = 1 - 1{T ≤ C, T < t}` of the one-subject estimator
(`tendsto_kaplanMeierOne_left`). -/
noncomputable def kaplanMeierOneLeft (T C : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if T ω ≤ C ω ∧ T ω < t then 0 else 1

/-- `kaplanMeierOneLeft` is the left limit of `kaplanMeierOne`. -/
theorem tendsto_kaplanMeierOne_left (t : ℝ) (ω : Ω) :
    Filter.Tendsto (fun s => kaplanMeierOne T C s ω) (nhdsWithin t (Iio t))
      (nhds (kaplanMeierOneLeft T C t ω)) := by
  simp only [kaplanMeierOne_eq, countingProcess, kaplanMeierOneLeft]
  by_cases hT : T ω < t
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hT] with s hs
    by_cases hTC : T ω ≤ C ω
    · simp [hTC, hT, hs.1.le]
    · simp [hTC]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s < t)
    have : ¬ T ω ≤ s := fun h => hT (h.trans_lt hs)
    simp [hT, this]

/-! ### Gill's representation for one subject -/

/-- The **counting measure** `dN(·, ω)` of one subject: a unit mass at the failure time if the
failure is observed, the zero measure if the subject is censored (`countingProcess_eq_measure`). -/
noncomputable def countingMeasure (T C : Ω → ℝ) (ω : Ω) : Measure ℝ :=
  if T ω ≤ C ω then Measure.dirac (T ω) else 0

/-- `N(t) = N((-∞, t])`: the counting process is the distribution function of `countingMeasure`. -/
theorem countingProcess_eq_measure (t : ℝ) (ω : Ω) :
    countingProcess T C t ω = (countingMeasure T C ω).real (Iic t) := by
  by_cases hTC : T ω ≤ C ω
  · by_cases hT : T ω ≤ t <;> simp [countingProcess, countingMeasure, hTC, hT, Measure.real]
  · simp [countingProcess, countingMeasure, hTC]

/-- **Gill's integrand** `H(s) = Ŝ(s-) / (S(s) Y(s))` for a survival function `S`, with Lean's
convention `x / 0 = 0` playing the role of Gill's indicator `J(s) = 1{Y(s) > 0}`. -/
noncomputable def kmIntegrand (T C : Ω → ℝ) (S : ℝ → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  kaplanMeierOneLeft T C s ω / (S s * atRiskProcess T C s ω)

/-- The **martingale term** `∫_{(0, t]} H d(N - A) = ∫_{(0, t]} H dN - ∫_{(0, t]} H Y dΛ` of
Gill's representation, where `A = ∫ Y dΛ` is the compensator for the hazard measure `Λ`. -/
noncomputable def kmMartingaleIntegral (T C : Ω → ℝ) (S : ℝ → ℝ) (Λ : Measure ℝ) (t : ℝ)
    (ω : Ω) : ℝ :=
  (∫ s in Ioc 0 t, kmIntegrand T C S s ω ∂(countingMeasure T C ω)) -
    ∫ s in Ioc 0 t, kmIntegrand T C S s ω * atRiskProcess T C s ω ∂Λ

/-- The **vanishing-risk remainder** `R(t) = ∫_{(0, t]} Ŝ(s-) / S(s) · 1{Y(s) = 0} dΛ(s)` of
Gill's representation of the Kaplan–Meier estimator. -/
noncomputable def kmRemainder (T C : Ω → ℝ) (S : ℝ → ℝ) (Λ : Measure ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in Ioc 0 t, kaplanMeierOneLeft T C s ω / S s *
    (if atRiskProcess T C s ω = 0 then 1 else 0) ∂Λ

/-- Before leaving the risk set the subject has not failed: `Ŝ(s-) = 1` for `s ≤ X`. -/
theorem kaplanMeierOneLeft_of_le_obsTime {s : ℝ} {ω : Ω} (hs : s ≤ obsTime T C ω) :
    kaplanMeierOneLeft T C s ω = 1 := by
  have : ¬ T ω < s := fun h => (lt_of_le_of_lt (hs.trans (min_le_left _ _)) h).false
  simp [kaplanMeierOneLeft, this]

private lemma kmIntegrand_mul_atRisk (S : ℝ → ℝ) (s : ℝ) (ω : Ω) :
    kmIntegrand T C S s ω * atRiskProcess T C s ω =
      (Iic (obsTime T C ω)).indicator (fun s => (S s)⁻¹) s := by
  by_cases hs : s ≤ obsTime T C ω
  · simp [kmIntegrand, atRiskProcess_eq_indicator, hs, kaplanMeierOneLeft_of_le_obsTime hs]
  · simp [kmIntegrand, atRiskProcess_eq_indicator, hs]

private lemma remainder_integrand (S : ℝ → ℝ) (s : ℝ) (ω : Ω) :
    kaplanMeierOneLeft T C s ω / S s * (if atRiskProcess T C s ω = 0 then 1 else 0) =
      if C ω < T ω then (Ioi (obsTime T C ω)).indicator (fun s => (S s)⁻¹) s else 0 := by
  by_cases hs : s ≤ obsTime T C ω
  · have : ¬ obsTime T C ω < s := not_lt.2 hs
    simp [atRiskProcess_eq_indicator, hs, this]
  · have hlt : obsTime T C ω < s := lt_of_not_ge hs
    by_cases hCT : C ω < T ω
    · have hTs : ¬ (T ω ≤ C ω ∧ T ω < s) := fun h => (h.1.trans_lt hCT).false
      simp [atRiskProcess_eq_indicator, hs, hlt, hCT, kaplanMeierOneLeft, hTs]
    · have hX : obsTime T C ω = T ω := min_eq_left (le_of_not_gt hCT)
      have hTs : T ω ≤ C ω ∧ T ω < s := ⟨le_of_not_gt hCT, hX ▸ hlt⟩
      simp [atRiskProcess_eq_indicator, hs, hCT, kaplanMeierOneLeft, hTs]

variable {S : ℝ → ℝ} {Λ : Measure ℝ}

/-- **Closed form of the martingale term.** If the subject is at risk at time `0` (`0 < X`) and
`S` solves the Volterra identity `1/S(b) - 1/S(a) = ∫_{(a, b]} dΛ/S` with `S(0) = 1`, then
`∫_{(0, t]} H d(N - A) = 1{T ≤ C, T ≤ t} / S(T) - (1/S(t ∧ X) - 1)`. -/
theorem kmMartingaleIntegral_eq {t : ℝ} {ω : Ω} (hX : 0 < obsTime T C ω) (ht : 0 ≤ t)
    (hS0 : S 0 = 1)
    (hS : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t → (S b)⁻¹ - (S a)⁻¹ = ∫ s in Ioc a b, (S s)⁻¹ ∂Λ) :
    kmMartingaleIntegral T C S Λ t ω =
      (if T ω ≤ C ω ∧ T ω ≤ t then (S (T ω))⁻¹ else 0) -
        ((S (min t (obsTime T C ω)))⁻¹ - 1) := by
  rw [kmMartingaleIntegral]
  congr 1
  · by_cases hTC : T ω ≤ C ω
    · have hXT : obsTime T C ω = T ω := min_eq_left hTC
      simp only [countingMeasure, hTC, ↓reduceIte]
      rw [restrict_dirac' measurableSet_Ioc]
      by_cases hT : T ω ≤ t
      · have hmem : T ω ∈ Ioc 0 t := ⟨hXT ▸ hX, hT⟩
        simp only [hmem, ite_true, integral_dirac, hT, and_self]
        simp [kmIntegrand, atRiskProcess, hTC, kaplanMeierOneLeft]
      · have hmem : T ω ∉ Ioc 0 t := fun h => hT h.2
        simp [hmem, hT]
    · simp [countingMeasure, hTC]
  · simp_rw [kmIntegrand_mul_atRisk]
    rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic,
      ← hS 0 _ le_rfl (le_min ht hX.le) (min_le_left _ _), hS0, inv_one]

/-- **Closed form of the remainder.** Under the hypotheses of `kmMartingaleIntegral_eq`,
`R(t) = 1{C < T, C ≤ t} (1/S(t) - 1/S(C))`: after censoring at `C`, every hazard increment on
`(C, t]` adds to `R`. -/
theorem kmRemainder_eq {t : ℝ} {ω : Ω} (hX : 0 < obsTime T C ω)
    (hS : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t → (S b)⁻¹ - (S a)⁻¹ = ∫ s in Ioc a b, (S s)⁻¹ ∂Λ) :
    kmRemainder T C S Λ t ω =
      if C ω < T ω ∧ C ω ≤ t then (S t)⁻¹ - (S (C ω))⁻¹ else 0 := by
  rw [kmRemainder]
  simp_rw [remainder_integrand]
  by_cases hCT : C ω < T ω
  · have hXC : obsTime T C ω = C ω := min_eq_right hCT.le
    simp only [hCT, ↓reduceIte, true_and]
    rw [setIntegral_indicator measurableSet_Ioi, hXC]
    by_cases hCt : C ω ≤ t
    · have hset : Ioc 0 t ∩ Ioi (C ω) = Ioc (C ω) t := by
        ext s
        simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
        exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨(hXC ▸ hX).trans h.1, h.2⟩, h.1⟩⟩
      simp only [hCt, ↓reduceIte]
      rw [hset, hS _ _ (hXC ▸ hX).le hCt le_rfl]
    · simp only [hCt, ↓reduceIte]
      have : Ioc 0 t ∩ Ioi (C ω) = ∅ := by
        ext s; simp only [mem_inter_iff, mem_Ioc, mem_Ioi, mem_empty_iff_false, iff_false]
        rintro ⟨⟨-, h⟩, h'⟩; exact hCt (h'.le.trans h)
      rw [this, Measure.restrict_empty, integral_zero_measure]
  · simp [hCT]

/-- **Gill's representation of the Kaplan–Meier estimator in continuous time** (one subject).
Let `S` be a survival function and `Λ` a hazard measure related by the Volterra identity
`1/S(b) - 1/S(a) = ∫_{(a, b]} dΛ/S` on `[0, t]`, with `S(0) = 1` (satisfied by
`S = ∏_{(0, ·]} (1 - dΛ)`, atoms of `Λ` allowed; see the module docstring for what it does not
determine). If the subject is at risk at time `0`, then
`Ŝ(t)/S(t) - 1 = -∫_{(0, t]} Ŝ(s-) / (S(s) Y(s)) d(N - A)(s) + R(t)` with the remainder
`R(t) = ∫_{(0, t]} Ŝ(s-)/S(s) 1{Y(s) = 0} dΛ(s)`.
The identity is pathwise; no positivity of `S` is needed because Lean's `x / 0 = 0` matches the
`J = 1{Y > 0}` convention. -/
theorem kaplanMeierOne_div_sub_one {t : ℝ} {ω : Ω} (hX : 0 < obsTime T C ω) (ht : 0 ≤ t)
    (hS0 : S 0 = 1)
    (hS : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t → (S b)⁻¹ - (S a)⁻¹ = ∫ s in Ioc a b, (S s)⁻¹ ∂Λ) :
    kaplanMeierOne T C t ω / S t - 1 =
      -kmMartingaleIntegral T C S Λ t ω + kmRemainder T C S Λ t ω := by
  rw [kmMartingaleIntegral_eq hX ht hS0 hS, kmRemainder_eq hX hS, kaplanMeierOne_eq,
    countingProcess]
  by_cases hTC : T ω ≤ C ω
  · have hXT : obsTime T C ω = T ω := min_eq_left hTC
    have hCT : ¬ C ω < T ω := not_lt.2 hTC
    by_cases hT : T ω ≤ t
    · simp [hTC, hT, hCT, hXT]
    · have hmin : min t (obsTime T C ω) = t := min_eq_left (hXT ▸ (lt_of_not_ge hT).le)
      simp [hTC, hT, hCT, hmin, div_eq_mul_inv]
  · have hCT : C ω < T ω := lt_of_not_ge hTC
    have hXC : obsTime T C ω = C ω := min_eq_right hCT.le
    by_cases hCt : C ω ≤ t
    · simp [hTC, hCT, hCt, hXC, div_eq_mul_inv]
    · have hmin : min t (obsTime T C ω) = t := min_eq_left (hXC ▸ (lt_of_not_ge hCt).le)
      simp [hTC, hCT, hCt, hmin, div_eq_mul_inv]

/-! ### When the remainder vanishes and when it is positive -/

/-- **No censoring, no remainder**: an uncensored subject (`T ≤ C`) leaves the risk set only by
failing, after which `Ŝ(s-) = 0`, so `R ≡ 0`. No hypothesis on `S` or `Λ` is needed. -/
theorem kmRemainder_eq_zero_of_le {t : ℝ} {ω : Ω} (hTC : T ω ≤ C ω) :
    kmRemainder T C S Λ t ω = 0 := by
  rw [kmRemainder]
  simp only [remainder_integrand, not_lt.2 hTC, ↓reduceIte]
  exact integral_zero _ _

/-- **No remainder before leaving the risk set**: `R(t) = 0` for `t ≤ X`. -/
theorem kmRemainder_eq_zero_of_le_obsTime {t : ℝ} {ω : Ω} (ht : t ≤ obsTime T C ω) :
    kmRemainder T C S Λ t ω = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
  have hY : atRiskProcess T C s ω ≠ 0 := by
    simp [atRiskProcess_eq_indicator, hs.2.trans ht]
  simp [hY]

/-- **The remainder is nonnegative** when `S` is positive and nonincreasing on `[0, t]`. -/
theorem kmRemainder_nonneg {t : ℝ} {ω : Ω} (hX : 0 < obsTime T C ω)
    (hS : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t → (S b)⁻¹ - (S a)⁻¹ = ∫ s in Ioc a b, (S s)⁻¹ ∂Λ)
    (hpos : 0 < S t) (hanti : AntitoneOn S (Icc 0 t)) :
    0 ≤ kmRemainder T C S Λ t ω := by
  rw [kmRemainder_eq hX hS]
  split_ifs with h
  · have hC0 : 0 ≤ C ω := (hX.trans_le (min_le_right _ _)).le
    have hle : S t ≤ S (C ω) := hanti ⟨hC0, h.2⟩ ⟨hC0.trans h.2, le_rfl⟩ h.2
    exact sub_nonneg.2 (inv_anti₀ hpos hle)
  · exact le_rfl

/-- **The remainder is positive after censoring**: if the subject is censored at `C < T` with
`C ≤ t` and the survival function strictly drops on `(C, t]` (`S(t) < S(C)`), then `R(t) > 0`. -/
theorem kmRemainder_pos {t : ℝ} {ω : Ω} (hX : 0 < obsTime T C ω)
    (hS : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t → (S b)⁻¹ - (S a)⁻¹ = ∫ s in Ioc a b, (S s)⁻¹ ∂Λ)
    (hCT : C ω < T ω) (hCt : C ω ≤ t) (hpos : 0 < S t) (hlt : S t < S (C ω)) :
    0 < kmRemainder T C S Λ t ω := by
  rw [kmRemainder_eq hX hS]
  simp only [hCT, hCt, and_self, ↓reduceIte]
  exact sub_pos.2 (inv_strictAnti₀ hpos hlt)

/-! ### The weighted compensator identity and the mean bias -/

section MeanBias

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

private lemma measurable_obsTime (hT : Measurable T) (hC : Measurable C) :
    Measurable (obsTime T C) :=
  hT.min hC

/-- Tonelli for the at-risk indicator: `E ∫_{(-∞, X]} g dΛ = ∫ g(s) P(X ≥ s) dΛ(s)`. -/
private lemma lintegral_setLIntegral_Iic_obsTime_eq [SFinite μ] {Λ : Measure ℝ} [SFinite Λ]
    (hX : Measurable (obsTime T C)) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ s in Iic (obsTime T C ω), g s ∂Λ ∂μ =
      ∫⁻ s, g s * μ {ω | s ≤ obsTime T C ω} ∂Λ := by
  have hset : MeasurableSet {p : Ω × ℝ | p.2 ≤ obsTime T C p.1} :=
    measurableSet_le measurable_snd (hX.comp measurable_fst)
  have hin : ∀ ω, ∫⁻ s in Iic (obsTime T C ω), g s ∂Λ =
      ∫⁻ s, {p : Ω × ℝ | p.2 ≤ obsTime T C p.1}.indicator (fun p => g p.2) (ω, s) ∂Λ := by
    intro ω
    rw [← lintegral_indicator measurableSet_Iic]
    rfl
  simp_rw [hin]
  have hm : AEMeasurable (Function.uncurry fun ω s =>
      {p : Ω × ℝ | p.2 ≤ obsTime T C p.1}.indicator (fun p => g p.2) (ω, s)) (μ.prod Λ) :=
    ((hg.comp measurable_snd).indicator hset).aemeasurable
  rw [lintegral_lintegral_swap hm]
  refine lintegral_congr fun s => ?_
  have : (fun ω => {p : Ω × ℝ | p.2 ≤ obsTime T C p.1}.indicator (fun p => g p.2) (ω, s)) =
      {ω | s ≤ obsTime T C ω}.indicator fun _ => g s := rfl
  rw [this, lintegral_indicator_const (measurableSet_le measurable_const hX)]

/-- **Weighted compensator identity** (independent censoring). For every measurable weight
`g ≥ 0`, `E ∫_{(-∞, X]} g dΛ = E[g(T) 1{T ≤ C}]`, i.e. `E ∫ g Y dΛ = E ∫ g dN`, with `Λ` the hazard
measure of the law of `T`. The indicator case `g = 1_B` is
`lintegral_hazardMeasure_inter_Iic_obsTime`; the general case follows from the measure identity
`Λ.withDensity (s ↦ P(X ≥ s)) = law of T on {T ≤ C}`. -/
theorem lintegral_setLIntegral_Iic_obsTime [IsProbabilityMeasure μ] (hT : Measurable T)
    (hC : Measurable C) (hind : IndepFun T C μ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ s in Iic (obsTime T C ω), g s ∂(hazardMeasure (μ.map T)) ∂μ =
      ∫⁻ ω in {ω | T ω ≤ C ω}, g (T ω) ∂μ := by
  set Λ := hazardMeasure (μ.map T) with hΛ
  have : SFinite Λ := by rw [hΛ, hazardMeasure]; infer_instance
  have hX := measurable_obsTime hT hC
  set h : ℝ → ℝ≥0∞ := fun s => μ {ω | s ≤ obsTime T C ω} with hh
  have hhm : Measurable h := Antitone.measurable fun a b hab =>
    measure_mono fun ω (hω : b ≤ obsTime T C ω) => hab.trans hω
  have hmeas : Λ.withDensity h = (μ.restrict {ω | T ω ≤ C ω}).map T := by
    ext B hB
    rw [withDensity_apply _ hB, Measure.map_apply hT hB,
      Measure.restrict_apply (hT hB), ← lintegral_indicator hB]
    have h1 : ∀ s, B.indicator h s = B.indicator 1 s * h s := fun s => by
      by_cases hs : s ∈ B <;> simp [hs]
    simp_rw [h1]
    rw [← lintegral_setLIntegral_Iic_obsTime_eq hX (measurable_one.indicator hB)]
    have h2 : ∀ ω, ∫⁻ s in Iic (obsTime T C ω), B.indicator 1 s ∂Λ =
        Λ (B ∩ Iic (obsTime T C ω)) := fun ω => by
      rw [lintegral_indicator_one hB, Measure.restrict_apply hB]
    simp_rw [h2]
    rw [hΛ, lintegral_hazardMeasure_inter_Iic_obsTime hT hC hind hB]
    rfl
  rw [lintegral_setLIntegral_Iic_obsTime_eq hX hg]
  have h3 : ∫⁻ s, g s * h s ∂Λ = ∫⁻ s, g s ∂(Λ.withDensity h) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hhm hg]
    exact lintegral_congr fun s => mul_comm _ _
  rw [h3, hmeas, lintegral_map hg hT]

/-- **The mean bias of `Ŝ/S` is the mean remainder** (Gill), for one subject in continuous time:
`E[Ŝ(t)/S(t) - 1] = E[R(t)]`. Hypotheses: `T`, `C` independent; `Λ` the hazard measure of the law
of `T`; `S` nonincreasing with `S(t) > 0`, `S(0) = 1`, `1/S` integrable on `(0, t]` and the
Volterra identity on `[0, t]`; the subject is at risk at time `0` almost surely.
The martingale term `∫ Ŝ₋/(SY) d(N - A)` has mean zero because `Ŝ₋/(SY) · Y = 1{s ≤ X}/S(s)` is a
fixed function of time times the at-risk indicator (`lintegral_setLIntegral_Iic_obsTime`). This is
the continuous-time counterpart of `integral_kaplanMeierProcess_div_sub_one`. -/
theorem integral_kaplanMeierOne_div_sub_one [IsProbabilityMeasure μ] (hT : Measurable T)
    (hC : Measurable C) (hind : IndepFun T C μ) {S : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hS0 : S 0 = 1) (hanti : Antitone S) (hpos : 0 < S t)
    (hint : IntegrableOn (fun s => (S s)⁻¹) (Ioc 0 t) (hazardMeasure (μ.map T)))
    (hS : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t →
      (S b)⁻¹ - (S a)⁻¹ = ∫ s in Ioc a b, (S s)⁻¹ ∂(hazardMeasure (μ.map T)))
    (hX : ∀ᵐ ω ∂μ, 0 < obsTime T C ω) :
    ∫ ω, (kaplanMeierOne T C t ω / S t - 1) ∂μ =
      ∫ ω, kmRemainder T C S (hazardMeasure (μ.map T)) t ω ∂μ := by
  set Λ := hazardMeasure (μ.map T) with hΛ
  have hXm := measurable_obsTime hT hC
  have hSm : Measurable S := hanti.measurable
  have hSle : ∀ {s}, s ≤ t → 0 < S s := fun hs => hpos.trans_le (hanti hs)
  -- the three pieces of the pathwise identity
  set A : Ω → ℝ := fun ω => if T ω ≤ C ω ∧ T ω ≤ t then (S (T ω))⁻¹ else 0 with hA
  set B : Ω → ℝ := fun ω => (S (min t (obsTime T C ω)))⁻¹ - 1 with hB
  set K : Ω → ℝ := fun ω => kaplanMeierOne T C t ω / S t - 1 with hK
  have hAset : MeasurableSet {ω | T ω ≤ C ω ∧ T ω ≤ t} :=
    (measurableSet_le hT hC).inter (measurableSet_le hT measurable_const)
  have hAi : Integrable A μ := by
    have hAm : Measurable A := Measurable.ite hAset (hSm.comp hT).inv measurable_const
    refine Integrable.of_bound hAm.aestronglyMeasurable (S t)⁻¹ (ae_of_all _ fun ω => ?_)
    simp only [hA]
    split_ifs with h
    · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hSle h.2))]
      exact inv_anti₀ hpos (hanti h.2)
    · simp [hpos.le]
  have hBi : Integrable B μ := by
    have hBm : Measurable B := (hSm.comp (measurable_const.min hXm)).inv.sub_const _
    refine Integrable.of_bound hBm.aestronglyMeasurable ((S t)⁻¹ + 1) (ae_of_all _ fun ω => ?_)
    have h1 : 0 < S (min t (obsTime T C ω)) := hSle (min_le_left _ _)
    calc ‖B ω‖ ≤ |(S (min t (obsTime T C ω)))⁻¹| + |1| := abs_sub _ _
      _ ≤ (S t)⁻¹ + 1 := by
          rw [abs_of_pos (inv_pos.2 h1), abs_one]
          gcongr
          exact hanti (min_le_left _ _)
  have hKi : Integrable K μ := by
    have hKeq : K = fun ω => (1 - countingProcess T C t ω) / S t - 1 :=
      funext fun ω => by simp only [hK, kaplanMeierOne_eq]
    rw [hKeq]
    refine Integrable.of_bound ((((measurable_const.sub (measurable_countingProcess hT hC t)
      ).div_const _).sub_const _).aestronglyMeasurable) ((S t)⁻¹ + 1)
      (ae_of_all _ fun ω => ?_)
    have h01 : countingProcess T C t ω = 0 ∨ countingProcess T C t ω = 1 := by
      simpa using countingProcess_mem (T := T) (C := C) t ω
    rcases h01 with h | h <;> rw [h]
    · rw [sub_zero, one_div, Real.norm_eq_abs]
      calc |(S t)⁻¹ - 1| ≤ |(S t)⁻¹| + |1| := abs_sub _ _
        _ = (S t)⁻¹ + 1 := by rw [abs_of_pos (inv_pos.2 hpos), abs_one]
    · simp only [sub_self, zero_div, zero_sub, norm_neg, norm_one]
      linarith [inv_pos.2 hpos]
  -- pathwise: `R = K + (A - B)` almost surely
  have hR : (fun ω => kmRemainder T C S Λ t ω) =ᵐ[μ] fun ω => K ω + (A ω - B ω) := by
    filter_upwards [hX] with ω hω
    have h1 := kaplanMeierOne_div_sub_one (Λ := Λ) hω ht hS0 hS
    rw [kmMartingaleIntegral_eq hω ht hS0 hS] at h1
    simp only [hK, hA, hB]
    linarith
  -- the martingale term has mean zero: `E A = E B`
  set g : ℝ → ℝ≥0∞ := (Ioc 0 t).indicator fun s => ENNReal.ofReal (S s)⁻¹ with hg
  have hgm : Measurable g := (hSm.inv.ennreal_ofReal).indicator measurableSet_Ioc
  have hgle : ∀ s, g s ≤ ENNReal.ofReal (S t)⁻¹ := fun s => by
    by_cases hs : s ∈ Ioc 0 t
    · simp only [hg, indicator_of_mem hs]
      exact ENNReal.ofReal_le_ofReal (inv_anti₀ hpos (hanti hs.2))
    · simp [hg, hs]
  set G : Ω → ℝ≥0∞ := {ω | T ω ≤ C ω}.indicator fun ω => g (T ω) with hG
  set H : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Iic (obsTime T C ω), g s ∂Λ with hH
  have hGm : Measurable G := (hgm.comp hT).indicator (measurableSet_le hT hC)
  have hHm : Measurable H := by
    have hmono : Monotone fun x => ∫⁻ s in Iic x, g s ∂Λ := fun a b hab =>
      lintegral_mono_set (Iic_subset_Iic.2 hab)
    exact hmono.measurable.comp hXm
  have hHfin : ∀ ω, H ω < ∞ := fun ω => by
    calc H ω ≤ ∫⁻ s, g s ∂Λ := setLIntegral_le_lintegral _ _
      _ = ∫⁻ s in Ioc 0 t, ENNReal.ofReal (S s)⁻¹ ∂Λ := lintegral_indicator measurableSet_Ioc _
      _ < ∞ := hint.lintegral_lt_top
  have hAG : A =ᵐ[μ] fun ω => (G ω).toReal := by
    filter_upwards [hX] with ω hω
    have hT0 : 0 < T ω := hω.trans_le (min_le_left _ _)
    simp only [hA, hG, hg]
    by_cases hTC : T ω ≤ C ω
    · by_cases hTt : T ω ≤ t
      · simp [hTC, hTt, hT0, (inv_pos.2 (hSle hTt)).le]
      · simp [hTC, hTt]
    · simp [hTC]
  have hBH : B =ᵐ[μ] fun ω => (H ω).toReal := by
    filter_upwards [hX] with ω hω
    set m := min t (obsTime T C ω)
    simp only [hB, hH, hg]
    rw [setLIntegral_indicator measurableSet_Ioc, Ioc_inter_Iic,
      ← integral_eq_lintegral_of_nonneg_ae ((ae_restrict_mem measurableSet_Ioc).mono fun s hs =>
        (inv_pos.2 (hSle (hs.2.trans (min_le_left _ _)))).le) hSm.inv.aestronglyMeasurable,
      ← hS 0 m le_rfl (le_min ht hω.le) (min_le_left _ _), hS0, inv_one]
  have hEAB : ∫ ω, A ω ∂μ = ∫ ω, B ω ∂μ := by
    rw [integral_congr_ae hAG, integral_congr_ae hBH,
      integral_toReal hGm.aemeasurable (ae_of_all _ fun ω => ?_),
      integral_toReal hHm.aemeasurable (ae_of_all _ hHfin), hG,
      lintegral_indicator (measurableSet_le hT hC),
      ← lintegral_setLIntegral_Iic_obsTime hT hC hind hgm]
    calc G ω ≤ ENNReal.ofReal (S t)⁻¹ := by
          by_cases h : ω ∈ {ω | T ω ≤ C ω}
          · simp only [hG, indicator_of_mem h]; exact hgle _
          · simp [hG, h]
      _ < ∞ := ENNReal.ofReal_lt_top
  have hadd := integral_add hKi (hAi.sub hBi)
  simp only [Pi.sub_apply] at hadd
  rw [integral_congr_ae hR, hadd, integral_sub hAi hBi, hEAB, sub_self, add_zero]

end MeanBias

/-! ### A nonzero example: exponential failure, censoring at time `1` -/

namespace ExpCensoredAtOne

open ProbabilityTheory Real

/-- The law of the failure time: the exponential distribution with rate `1`. -/
noncomputable abbrev μ₀ : Measure ℝ := expMeasure 1

instance : IsProbabilityMeasure μ₀ := isProbabilityMeasure_expMeasure one_pos

/-- The failure time `T(ω) = ω`, on the canonical space `(ℝ, Exp(1))`. -/
abbrev T₀ : ℝ → ℝ := id

/-- Deterministic censoring at time `1`: `C ≡ 1`. -/
abbrev C₀ : ℝ → ℝ := fun _ => 1

/-- The survival function `S(t) = e^{-t}` of `Exp(1)` (`measureReal_Ioi`). -/
noncomputable abbrev S₀ : ℝ → ℝ := fun s => exp (-s)

/-- `S` is the survival function of `T`: `P(T > t) = e^{-t}` for `t ≥ 0`. -/
theorem measureReal_Ioi {t : ℝ} (ht : 0 ≤ t) : μ₀.real (Ioi t) = exp (-t) := by
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real,
    cdf_expMeasure_eq one_pos]
  simp [ht]

/-- **The Volterra identity** for `S(t) = e^{-t}` and the hazard measure `Λ = Lebesgue`
(constant hazard rate `1`): `e^b - e^a = ∫_{(a, b]} e^s ds`. -/
theorem volterra {a b : ℝ} (hab : a ≤ b) :
    (S₀ b)⁻¹ - (S₀ a)⁻¹ = ∫ s in Ioc a b, (S₀ s)⁻¹ := by
  simp only [S₀, exp_neg, inv_inv]
  rw [← intervalIntegral.integral_of_le hab, integral_exp]

/-- No atoms: `P(T ≥ s) = P(T > s) = e^{-s}` for `s ≥ 0`. -/
lemma measure_Ici {s : ℝ} (hs : 0 ≤ s) : μ₀ (Ici s) = ENNReal.ofReal (exp (-s)) := by
  have h0 : μ₀ {s} = 0 :=
    withDensity_absolutelyContinuous volume (gammaPDF 1 1) Real.volume_singleton
  rw [← measure_congr (Ioi_ae_eq_Ici' h0), ← measureReal_Ioi hs, ofReal_measureReal]

/-- **`Λ` is the hazard measure of `Exp(1)`**: on `(0, ∞)` the hazard measure
`dF(s) / F[s, ∞)` (`hazardMeasure`) is Lebesgue measure, i.e. the hazard rate is `1`. -/
theorem hazardMeasure_restrict_Ioi :
    (hazardMeasure μ₀).restrict (Ioi 0) = volume.restrict (Ioi 0) := by
  have hf : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
  have hdef : hazardMeasure μ₀ =
      volume.withDensity (exponentialPDF 1 * fun s => (μ₀ (Ici s))⁻¹) :=
    (withDensity_mul volume hf (measurable_measure_Ici μ₀).inv).symm
  rw [hdef, restrict_withDensity measurableSet_Ioi]
  conv_rhs => rw [← withDensity_one (μ := volume.restrict (Ioi (0 : ℝ)))]
  refine withDensity_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) => ?_)
  simp only [Pi.mul_apply, Pi.one_apply, exponentialPDF_of_nonneg hs.le, one_mul,
    measure_Ici hs.le]
  exact ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 (exp_pos _)).ne' ENNReal.ofReal_ne_top

/-- The hazard measure `Λ` of `Exp(1)`. -/
noncomputable abbrev Λ₀ : Measure ℝ := hazardMeasure μ₀

/-- **The Volterra identity for the true hazard**: `1/S(b) - 1/S(a) = ∫_{(a, b]} dΛ/S` on
`[0, ∞)`, so `S(t) = e^{-t}` is `∏_{(0, t]} (1 - dΛ)`. -/
theorem volterra_hazard {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (S₀ b)⁻¹ - (S₀ a)⁻¹ = ∫ s in Ioc a b, (S₀ s)⁻¹ ∂Λ₀ := by
  have hsub : Ioc a b ⊆ Ioi 0 := fun s hs => ha.trans_lt hs.1
  rw [← Measure.restrict_restrict_of_subset hsub, hazardMeasure_restrict_Ioi,
    Measure.restrict_restrict_of_subset hsub, volterra hab]

/-- The history filtration `ℱₜ = σ(N(u), Nᶜ(u) : u ≤ t)` of the model. -/
noncomputable abbrev ℱ₀ : Filtration ℝ (inferInstance : MeasurableSpace ℝ) :=
  historyFiltration (T := T₀) (C := C₀) measurable_id measurable_const

/-- **The remainder is the censoring indicator times `e^t - e`**: for `t ≥ 1`,
`R(t) = 1{T > 1} (1/S(t) - 1/S(1)) = 1{T > 1} (e^t - e)`. -/
theorem kmRemainder_eq_indicator {t : ℝ} (ht : 1 ≤ t) :
    kmRemainder T₀ C₀ S₀ Λ₀ t = (Ioi 1).indicator fun _ => exp t - exp 1 := by
  funext ω
  by_cases hω : 1 < ω
  · have hX : 0 < obsTime T₀ C₀ ω := by simp [obsTime, min_eq_right hω.le]
    rw [kmRemainder_eq hX fun a b ha hab _ => volterra_hazard ha hab]
    simp [hω, ht, S₀, exp_neg]
  · rw [kmRemainder_eq_zero_of_le (not_lt.1 hω)]
    simp [hω]

/-- The remainder is a multiple of the censoring process at time `1`. -/
lemma kmRemainder_eq_mul_censoringProcess {t : ℝ} (ht : 1 ≤ t) :
    kmRemainder T₀ C₀ S₀ Λ₀ t = fun ω => (exp t - exp 1) * censoringProcess T₀ C₀ 1 ω := by
  rw [kmRemainder_eq_indicator ht]
  funext ω
  by_cases hω : 1 < ω <;> simp [censoringProcess, hω]

/-- The remainder `R(t)` is known at time `1`: censoring at `1` determines it. -/
lemma stronglyMeasurable_kmRemainder {t : ℝ} (ht : 1 ≤ t) :
    StronglyMeasurable[ℱ₀ 1] (kmRemainder T₀ C₀ S₀ Λ₀ t) := by
  rw [kmRemainder_eq_mul_censoringProcess ht]
  exact ((measurable_observedProcess_history (T := T₀) (C := C₀) measurable_id measurable_const
    le_rfl).snd.const_mul _).stronglyMeasurable

/-- The remainder is integrable (it is bounded). -/
lemma integrable_kmRemainder {t : ℝ} (ht : 1 ≤ t) : Integrable (kmRemainder T₀ C₀ S₀ Λ₀ t) μ₀ := by
  rw [kmRemainder_eq_indicator ht]
  exact (integrable_const _).indicator measurableSet_Ioi

/-- **Conditional expectation given the history at time `1`**:
`E[R(t) | ℱ₁] = R(t) = 1{T > 1} (e^t - e)`. -/
theorem condExp_kmRemainder {t : ℝ} (ht : 1 ≤ t) :
    μ₀[kmRemainder T₀ C₀ S₀ Λ₀ t | ℱ₀ 1] = (Ioi 1).indicator fun _ => exp t - exp 1 := by
  rw [condExp_of_stronglyMeasurable ((ℱ₀).le 1) (stronglyMeasurable_kmRemainder ht)
    (integrable_kmRemainder ht), kmRemainder_eq_indicator ht]

/-- **The continuous-time Kaplan–Meier remainder is genuinely nonzero**: for `t > 1`,
`E[R(t) | ℱ₁]` is not a.e. zero. -/
theorem condExp_kmRemainder_ne_zero {t : ℝ} (ht : 1 < t) :
    ¬ μ₀[kmRemainder T₀ C₀ S₀ Λ₀ t | ℱ₀ 1] =ᵐ[μ₀] 0 := by
  rw [condExp_kmRemainder ht.le, Filter.EventuallyEq, ae_iff]
  have hc : exp t - exp 1 ≠ 0 := sub_ne_zero.2 (exp_injective.ne ht.ne')
  have hsub : Ioi (1 : ℝ) ⊆
      {ω | ¬ (Ioi 1).indicator (fun _ => exp t - exp 1) ω = (0 : ℝ → ℝ) ω} := fun ω hω => by
    simp [show (1 : ℝ) < ω from hω, hc]
  intro h
  have h1 := measure_mono_null hsub h
  rw [← ofReal_measureReal, measureReal_Ioi zero_le_one, ENNReal.ofReal_eq_zero] at h1
  exact (exp_pos _).not_ge h1

/-- **The mean of the remainder**: `E[R(t)] = P(T > 1) (e^t - e) = e^{t-1} - 1` for `t ≥ 1`. -/
theorem integral_kmRemainder {t : ℝ} (ht : 1 ≤ t) :
    ∫ ω, kmRemainder T₀ C₀ S₀ Λ₀ t ω ∂μ₀ = exp (t - 1) - 1 := by
  rw [kmRemainder_eq_indicator ht, integral_indicator_const _ measurableSet_Ioi,
    measureReal_Ioi zero_le_one, smul_eq_mul, mul_sub, ← exp_add, ← exp_add]
  simp [sub_eq_neg_add]

/-- **The mean bias of `Ŝ/S` is the mean remainder** in this model:
`E[Ŝ(t)/S(t)] - 1 = E[R(t)]` for `t ≥ 1`. Both sides are computed independently (the left side
from `Ŝ(t) = 1 - N(t)` and `P(T ≤ 1) = 1 - e^{-1}`), without the general theorem
`ContinuousTime.integral_kaplanMeierOne_div_sub_one`, which the test file also applies here. -/
theorem integral_kaplanMeierOne_div_sub_one_eq_integral_kmRemainder {t : ℝ} (ht : 1 ≤ t) :
    ∫ ω, (kaplanMeierOne T₀ C₀ t ω / S₀ t - 1) ∂μ₀ = ∫ ω, kmRemainder T₀ C₀ S₀ Λ₀ t ω ∂μ₀ := by
  have hfun : (fun ω => kaplanMeierOne T₀ C₀ t ω / S₀ t - 1) =
      fun ω => (Ioi 1).indicator (fun _ => exp t) ω - 1 := by
    funext ω
    rw [kaplanMeierOne_eq]
    by_cases hω : 1 < ω
    · have : ¬ ω ≤ 1 := not_le.2 hω
      simp [countingProcess, hω, this, S₀, exp_neg]
    · have hω' : ω ≤ 1 := not_lt.1 hω
      simp [countingProcess, hω, hω', hω'.trans ht]
  rw [hfun, integral_sub ((integrable_const _).indicator measurableSet_Ioi) (integrable_const _),
    integral_indicator_const _ measurableSet_Ioi, measureReal_Ioi zero_le_one, integral_const,
    probReal_univ, integral_kmRemainder ht, smul_eq_mul, ← exp_add, smul_eq_mul, mul_one]
  ring_nf

end ExpCensoredAtOne

end MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime
