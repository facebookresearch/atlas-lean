/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Analysis.SpecificLimits.Basic
import MathlibExt.Probability.CondExpAntitoneLimit

/-!
# Optional stopping in continuous time

For a continuous-path martingale and bounded stopping times `σ ≤ τ`, the value at `σ` is the
conditional expectation of the value at `τ` given the stopped σ-algebra at `σ`.
-/

public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace MathlibExt.Probability.ContinuousOptionalStoppingWanted.Martingale

private noncomputable def roundUp (d t : ℝ≥0) : ℝ≥0 := (⌈t * d⌉₊ : ℝ≥0) / d

private theorem isStoppingTime_roundUp {Ω : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {r : Ω → ℝ≥0}
    (hr : IsStoppingTime ℱ fun ω ↦ (r ω : WithTop ℝ≥0)) {d : ℝ≥0} (hd : 0 < d) :
    IsStoppingTime ℱ fun ω ↦ ↑(roundUp d (r ω)) := by
  intro t
  let s : ℝ≥0 := (⌊t * d⌋₊ : ℝ≥0) / d
  have hst : s ≤ t := (div_le_iff₀ hd).2 (Nat.floor_le (bot_le : 0 ≤ t * d))
  -- The event of stopping by `t` is already known at the preceding grid point `s`.
  have hset : {ω | (roundUp d (r ω) : WithTop ℝ≥0) ≤ t} = {ω | (r ω : WithTop ℝ≥0) ≤ s} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe, roundUp, s, div_le_iff₀ hd, le_div_iff₀ hd,
      ← Nat.le_floor_iff (bot_le : 0 ≤ t * d), Nat.ceil_le]
  rw [hset]
  exact ℱ.mono hst _ (hr s)

private theorem tendsto_roundUp (t : ℝ≥0) :
    Tendsto (fun k : ℕ ↦ roundUp (2 ^ k) t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  exact (tendsto_nat_ceil_mul_div_atTop t.2).comp
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2))

private theorem stoppedValue_ae_eq_terminal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ) (hcont : ∀ ω, Continuous fun t ↦ M t ω)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) {n : ℝ≥0} (hτn : ∀ ω, τ ω ≤ n) :
    stoppedValue M τ =ᵐ[μ] μ[M n | hτ.measurableSpace] := by
  let r (ω : Ω) := (τ ω).untopA
  have hr (ω : Ω) : (r ω : WithTop ℝ≥0) = τ ω := by
    have hfin := ((hτn ω).trans_lt (WithTop.coe_lt_top n)).ne
    simp only [r, WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
  have hrStop : IsStoppingTime ℱ fun ω ↦ (r ω : WithTop ℝ≥0) := by simpa only [hr] using hτ
  -- Cap the rounded times at the common terminal time to keep the same terminal value.
  let ρ (k : ℕ) (ω : Ω) : WithTop ℝ≥0 := min (↑(roundUp (2 ^ k) (r ω))) (↑n)
  have hρ (k : ℕ) : IsStoppingTime ℱ (ρ k) :=
    (isStoppingTime_roundUp hrStop (pow_pos zero_lt_two k)).min_const n
  have hle (k : ℕ) : τ ≤ ρ k := by
    intro ω
    refine le_min ?_ (hτn ω)
    rw [← hr]
    exact WithTop.coe_le_coe.mpr ((le_div_iff₀ (pow_pos zero_lt_two k)).2
      (Nat.le_ceil _))
  let m (k : ℕ) := (hρ k).measurableSpace
  have hm (k : ℕ) : m k ≤ ‹MeasurableSpace Ω› := (hρ k).measurableSpace_le
  have heq (k : ℕ) : stoppedValue M (ρ k) =ᵐ[μ] μ[M n | m k] := by
    apply hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hρ k)
      (fun ω ↦ min_le_right _ _)
    refine (Set.countable_range (fun j : ℕ ↦ min (↑((j : ℝ≥0) / 2 ^ k) : WithTop ℝ≥0) ↑n)).mono ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨⌈r ω * 2 ^ k⌉₊, rfl⟩
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun k ↦ (μ[M n | m k]) ω) atTop
      (𝓝 (stoppedValue M τ ω)) := by
    filter_upwards [ae_all_iff.2 heq] with ω hω
    refine Tendsto.congr (fun k ↦ hω k) ((hcont ω).continuousAt.tendsto.comp ?_)
    have hrn : r ω ≤ n := WithTop.untopA_le (hτn ω)
    simpa only [ρ, stoppedValue, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe,
      min_eq_left hrn] using
      (tendsto_roundUp (r ω)).min (tendsto_const_nhds (x := n))
  have hint := ((hM.integrable n).uniformIntegrable_condExp hm).memLp_of_ae_tendsto hlim
  have hmeas := (measurable_stoppedValue
    (hM.stronglyAdapted.isStronglyProgressive_of_continuous hcont) hτ).stronglyMeasurable
  have hsub : hτ.measurableSpace ≤ ⨅ k, m k :=
    le_iInf fun k ↦ hτ.measurableSpace_mono (hρ k) (hle k)
  -- Identify the limit at the intersection, then condition down to the stopped σ-algebra.
  have hcond := CondExpAntitoneLimit.condExp_antitone_limit_eq (M n) m hm (hM.integrable n)
    (stoppedValue M τ) hlim (memLp_one_iff_integrable.mp hint) (hmeas.mono hsub)
  have htower := (condExp_congr_ae (m := hτ.measurableSpace) hcond).trans
    (condExp_condExp_of_le hsub ((iInf_le m 0).trans (hm 0)))
  rwa [condExp_of_stronglyMeasurable hτ.measurableSpace_le hmeas
    (memLp_one_iff_integrable.mp hint)] at htower

/-- **Optional stopping theorem in continuous time.** Let `M` be a real martingale indexed by
`ℝ≥0` with continuous paths, on a probability space, and let `σ ≤ τ` be stopping times bounded by
a constant `n`. Then `M_σ = E[M_τ | F_σ]` almost surely (Le Gall, *Brownian Motion, Martingales,
and Stochastic Calculus*, Chapter 3, section "Optional stopping theorems", stated there for
uniformly integrable martingales with right-continuous paths; a martingale on `[0, n]` is
uniformly integrable). -/
theorem stoppedValue_ae_eq_condExp_of_le_of_continuous {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) {n : ℝ≥0}
    (hτn : ∀ ω, τ ω ≤ n) :
    stoppedValue M σ =ᵐ[μ] μ[stoppedValue M τ | hσ.measurableSpace] := by
  have hσn := stoppedValue_ae_eq_terminal hM hcont hσ (fun ω ↦ (hστ ω).trans (hτn ω))
  have hτeq := stoppedValue_ae_eq_terminal hM hcont hτ hτn
  exact hσn.trans ((condExp_congr_ae hτeq).trans
    (condExp_condExp_of_le (hσ.measurableSpace_mono hτ hστ) hτ.measurableSpace_le)).symm

end MathlibExt.Probability.ContinuousOptionalStoppingWanted.Martingale
