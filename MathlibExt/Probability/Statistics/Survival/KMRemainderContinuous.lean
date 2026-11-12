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
Among positive functions this identity characterises the product integral
`S = ∏_{(0, ·]} (1 - dΛ)`, atoms of `Λ` included (at an atom,
`1/S(s) - 1/S(s-) = ΔΛ(s)/S(s)` is `S(s) = S(s-)(1 - ΔΛ(s))`). Mathlib has no
Lebesgue–Stieltjes product integral (its construction is the unmerged task T77), so, as in
`MathlibExt/Probability/Statistics/ContinuousProductIntegral.lean`, it enters as this explicit
hypothesis. With `Ŝ` the Kaplan–Meier estimator (`kaplanMeierOne`, the grouped-data
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
  after censoring at `C < t` if `S(t) < S(C)`.
* **Exponential failure, censoring at time `1`** (`ExpCensoredAtOne`): `T ~ Exp(1)`, `C ≡ 1`,
  `S(t) = e^{-t}` (`measureReal_Ioi`), and `Λ = hazardMeasure (Exp(1))` is Lebesgue measure on
  `(0, ∞)` (`hazardMeasure_restrict_Ioi`), so the Volterra hypothesis holds (`volterra_hazard`).
  For `t ≥ 1`, `R(t) = 1{T > 1} (e^t - e)` (`kmRemainder_eq_indicator`) is known at time `1`, and
  `E[R(t) | ℱ₁] = R(t)` (`condExp_kmRemainder`) is not a.e. zero for `t > 1`
  (`condExp_kmRemainder_ne_zero`), with `ℱ` the history filtration `historyFiltration`. The mean
  bias is `E[Ŝ(t)/S(t)] - 1 = E[R(t)] = e^{t-1} - 1` (`integral_kaplanMeierOne_div_sub_one`,
  `integral_kmRemainder`), both sides computed independently.

## Scope

* **One subject.** Gill's theorem is for `n` subjects; the `n`-subject pathwise identity needs
  Lebesgue–Stieltjes integration by parts for the product-limit estimator, which is not
  formalized here. The `n`-subject discrete-grid version is `kaplanMeierProcess_div_sub_one`.
* **The product integral is a hypothesis** (the Volterra identity above), not constructed.
* **Mean bias in general.** `E[Ŝ(t)/S(t) - 1] = E[R(t)]` needs the martingale term to have mean
  zero, i.e. a continuous-time stochastic integral against `N - A`; the repository has the
  compensator (`martingale_compensatedProcess`) but not that integral. The identity is verified
  in the exponential model only.

## Source receipt (reuse search, 2026-11-12)

Mathlib v4.35.0 has no product integral and no continuous-time Kaplan–Meier estimator. Reused:
`obsTime`, `countingProcess`, `censoringProcess`, `atRiskProcess`, `atRiskProcess_eq_indicator`,
`hazardMeasure`, `measurable_measure_Ici`, `historyFiltration`,
`measurable_observedProcess_history` (`CountingProcess.lean`); `CensoredData`,
`CensoredData.kmSurvival` (`KaplanMeier.lean`); `ProbabilityTheory.expMeasure`,
`cdf_expMeasure_eq`, `exponentialPDF_of_nonneg`, `integral_exp`, `withDensity_mul`,
`restrict_withDensity`, `condExp_of_stronglyMeasurable` (Mathlib). The discrete statements of
`KMRemainder.lean` are the time-discrete counterparts.

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

open MeasureTheory Set
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
`1/S(b) - 1/S(a) = ∫_{(a, b]} dΛ/S` on `[0, t]`, with `S(0) = 1` (this identity characterises
`S = ∏_{(0, ·]} (1 - dΛ)` among positive functions, atoms of `Λ` allowed). If the subject is at
risk at time `0`, then
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
`C < t` and the survival function strictly drops on `(C, t]` (`S(t) < S(C)`), then `R(t) > 0`. -/
theorem kmRemainder_pos {t : ℝ} {ω : Ω} (hX : 0 < obsTime T C ω)
    (hS : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t → (S b)⁻¹ - (S a)⁻¹ = ∫ s in Ioc a b, (S s)⁻¹ ∂Λ)
    (hCT : C ω < T ω) (hCt : C ω ≤ t) (hpos : 0 < S t) (hlt : S t < S (C ω)) :
    0 < kmRemainder T C S Λ t ω := by
  rw [kmRemainder_eq hX hS]
  simp only [hCT, hCt, and_self, ↓reduceIte]
  exact sub_pos.2 (inv_strictAnti₀ hpos hlt)

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
from `Ŝ(t) = 1 - N(t)` and `P(T ≤ 1) = 1 - e^{-1}`), so the martingale term of
`kaplanMeierOne_div_sub_one` has mean zero here. -/
theorem integral_kaplanMeierOne_div_sub_one {t : ℝ} (ht : 1 ≤ t) :
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
