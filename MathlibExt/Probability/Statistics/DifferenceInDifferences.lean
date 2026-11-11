/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Difference-in-differences identification (2×2 design)

Two groups and two periods. A unit in the treated group `G` is exposed to treatment between the
pre and post periods; units in `Gᶜ` stay untreated. With potential outcomes `Y₀pre, Y₁pre,
Y₀post, Y₁post` and observed outcomes `observed G Y₀ Y₁` (consistency), the difference in the
group means of the observed pre-to-post changes identifies the average treatment effect on the
treated in the post period under two assumptions: no anticipation (the treated group's pre-period
outcome does not respond to the upcoming treatment) and parallel trends (the untreated potential
outcomes change by the same amount, on average, in both groups). Group means are set averages:
for a probability measure with `0 < μ G < 1` they are the conditional means of the source. No
positivity or finiteness of the group masses is assumed, and only integrability on the treated
group is needed. Mathlib's set average takes the junk value `0` when the group has measure `0`
or `∞`, or when the function is not integrable on the group (for example an untreated trend that
is not integrable on the control group); the identities hold in all these cases, and in the
source setting (integrable outcomes) every average is the corresponding conditional mean.

This is the population identification step only; estimation, two-way fixed-effects regression,
staggered adoption and inference are not covered.

## Main definitions

* `didEstimand μ G Ypre Ypost`: `⨍_G (Ypost - Ypre) - ⨍_{Gᶜ} (Ypost - Ypre)`.
* `attPost μ G Y₀post Y₁post`: `⨍_G (Y₁post - Y₀post)`, the post-period ATT.

## Main results

* `didEstimand_observed_eq_attPost_add`: under no anticipation, the DiD of observed outcomes is
  the ATT plus the DiD of the untreated potential outcomes (the parallel-trends gap).
* `didEstimand_observed_eq_attPost`: under no anticipation and parallel trends, the DiD of
  observed outcomes equals the ATT.

## References

* J. Roth, P. H. C. Sant'Anna, A. Bilinski, J. Poe, *What's trending in difference-in-differences?
  A synthesis of the recent econometrics literature*, J. Econometrics 235 (2023), 2218–2244,
  §2.2–2.3 (Assumptions 1 and 2, eq. (2)).
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Probability.Statistics.DifferenceInDifferences

open MathlibExt.Probability.Causality

/-- The 2×2 difference-in-differences estimand of Roth et al. (2023), eq. (2):
`E[Y_post - Y_pre | G] - E[Y_post - Y_pre | Gᶜ]`, where `G` is the treated group and the
conditional means are set averages over the group events. For a probability measure with
`0 < μ G < 1` and integrable outcomes these are the conditional means of the source; if a group
has measure `0` or `∞`, or the difference is not integrable on it, its set average is Mathlib's
junk value `0`. -/
noncomputable def didEstimand {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : Set Ω)
    (Ypre Ypost : Ω → ℝ) : ℝ :=
  (⨍ ω in G, (Ypost ω - Ypre ω) ∂μ) - ⨍ ω in Gᶜ, (Ypost ω - Ypre ω) ∂μ

/-- The average treatment effect on the treated in the post period,
`τ₂ = E[Y_post(1) - Y_post(0) | G]` (a set average over `G`; junk `0` if `μ G ∈ {0, ∞}` or the
difference is not integrable on `G`). -/
noncomputable def attPost {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : Set Ω)
    (Y₀post Y₁post : Ω → ℝ) : ℝ :=
  ⨍ ω in G, (Y₁post ω - Y₀post ω) ∂μ

/-- Bias decomposition of the 2×2 DiD under no anticipation: the DiD of observed outcomes is the
post-period ATT plus the DiD of the untreated potential outcomes (the parallel-trends gap).
Only integrability on the treated group is needed; no positivity or finiteness of the group
masses and no integrability on `Gᶜ` is assumed: the control-group term is the same set average
on both sides, so the identity also holds when it takes Mathlib's junk value. -/
theorem didEstimand_observed_eq_attPost_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {G : Set Ω} (hG : MeasurableSet G) {Y₀pre Y₁pre Y₀post Y₁post : Ω → ℝ}
    (h₀pre : IntegrableOn Y₀pre G μ) (h₀post : IntegrableOn Y₀post G μ)
    (h₁post : IntegrableOn Y₁post G μ)
    (hNA : Y₁pre =ᵐ[μ.restrict G] Y₀pre) :
    didEstimand μ G (observed G Y₀pre Y₁pre) (observed G Y₀post Y₁post) =
      attPost μ G Y₀post Y₁post + didEstimand μ G Y₀pre Y₀post := by
  unfold didEstimand attPost
  have hObsPreG : ∀ ω : Ω, ω ∈ G → observed G Y₀pre Y₁pre ω = Y₁pre ω := by
    intro ω hω
    have hnc : ω ∉ Gᶜ := by simpa using hω
    simp [observed, Set.indicator_of_mem hω, Set.indicator_of_notMem hnc]
  have hObsPostG : ∀ ω : Ω, ω ∈ G → observed G Y₀post Y₁post ω = Y₁post ω := by
    intro ω hω
    have hnc : ω ∉ Gᶜ := by simpa using hω
    simp [observed, Set.indicator_of_mem hω, Set.indicator_of_notMem hnc]
  have hObsPreGc : ∀ ω : Ω, ω ∈ Gᶜ → observed G Y₀pre Y₁pre ω = Y₀pre ω := by
    intro ω hω
    have hω' : ω ∉ G := by simpa using hω
    simp [observed, Set.indicator_of_notMem hω', Set.indicator_of_mem hω]
  have hObsPostGc : ∀ ω : Ω, ω ∈ Gᶜ → observed G Y₀post Y₁post ω = Y₀post ω := by
    intro ω hω
    have hω' : ω ∉ G := by simpa using hω
    simp [observed, Set.indicator_of_notMem hω', Set.indicator_of_mem hω]
  have hDiffG : (fun ω => observed G Y₀post Y₁post ω - observed G Y₀pre Y₁pre ω)
      =ᵐ[μ.restrict G] (fun ω => Y₁post ω - Y₁pre ω) := by
    filter_upwards [ae_restrict_mem hG] with ω hω
    rw [hObsPreG ω hω, hObsPostG ω hω]
  have hAvgG_obs : (⨍ ω in G, (observed G Y₀post Y₁post ω - observed G Y₀pre Y₁pre ω) ∂μ)
      = ⨍ ω in G, (Y₁post ω - Y₁pre ω) ∂μ :=
    average_congr hDiffG
  have hNAdiff : (fun ω => Y₁post ω - Y₁pre ω)
      =ᵐ[μ.restrict G] (fun ω => Y₁post ω - Y₀pre ω) := by
    filter_upwards [hNA] with ω hω
    rw [hω]
  have hAvgG_NA : (⨍ ω in G, (Y₁post ω - Y₁pre ω) ∂μ)
      = ⨍ ω in G, (Y₁post ω - Y₀pre ω) ∂μ :=
    average_congr hNAdiff
  have hDiffGc : (fun ω => observed G Y₀post Y₁post ω - observed G Y₀pre Y₁pre ω)
      =ᵐ[μ.restrict Gᶜ] (fun ω => Y₀post ω - Y₀pre ω) := by
    filter_upwards [ae_restrict_mem hG.compl] with ω hω
    rw [hObsPreGc ω hω, hObsPostGc ω hω]
  have hAvgGc_obs : (⨍ ω in Gᶜ, (observed G Y₀post Y₁post ω - observed G Y₀pre Y₁pre ω) ∂μ)
      = ⨍ ω in Gᶜ, (Y₀post ω - Y₀pre ω) ∂μ :=
    average_congr hDiffGc
  have h1 : (⨍ ω in G, (Y₁post ω - Y₀pre ω) ∂μ)
      = (⨍ ω in G, Y₁post ω ∂μ) - (⨍ ω in G, Y₀pre ω ∂μ) :=
    setAverage_sub h₁post h₀pre
  have h2 : (⨍ ω in G, (Y₁post ω - Y₀post ω) ∂μ)
      = (⨍ ω in G, Y₁post ω ∂μ) - (⨍ ω in G, Y₀post ω ∂μ) :=
    setAverage_sub h₁post h₀post
  have h3 : (⨍ ω in G, (Y₀post ω - Y₀pre ω) ∂μ)
      = (⨍ ω in G, Y₀post ω ∂μ) - (⨍ ω in G, Y₀pre ω ∂μ) :=
    setAverage_sub h₀post h₀pre
  rw [hAvgG_obs, hAvgG_NA, hAvgGc_obs, h1, h2, h3]
  ring

/-- **Identification of the ATT by 2×2 difference-in-differences** (Roth et al. 2023, §2.3):
under no anticipation and parallel trends in the untreated potential outcomes, the DiD of
observed group means equals the post-period average treatment effect on the treated. In the
source setting (a probability measure with `0 < μ G < 1` and integrable outcomes) the hypotheses
hold and the set averages are the source's conditional means. -/
theorem didEstimand_observed_eq_attPost {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {G : Set Ω} (hG : MeasurableSet G) {Y₀pre Y₁pre Y₀post Y₁post : Ω → ℝ}
    (h₀pre : IntegrableOn Y₀pre G μ) (h₀post : IntegrableOn Y₀post G μ)
    (h₁post : IntegrableOn Y₁post G μ)
    (hNA : Y₁pre =ᵐ[μ.restrict G] Y₀pre)
    (hPT : ⨍ ω in G, (Y₀post ω - Y₀pre ω) ∂μ = ⨍ ω in Gᶜ, (Y₀post ω - Y₀pre ω) ∂μ) :
    didEstimand μ G (observed G Y₀pre Y₁pre) (observed G Y₀post Y₁post) =
      attPost μ G Y₀post Y₁post := by
  have hGap : didEstimand μ G Y₀pre Y₀post = 0 := by
    unfold didEstimand
    exact sub_eq_zero.mpr hPT
  have hAdd := didEstimand_observed_eq_attPost_add hG h₀pre h₀post h₁post hNA
  rw [hAdd, hGap, add_zero]

end MathlibExt.Probability.Statistics.DifferenceInDifferences
