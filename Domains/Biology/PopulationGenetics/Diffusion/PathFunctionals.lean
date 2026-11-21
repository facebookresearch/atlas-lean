/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
public import Domains.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Markov
import Domains.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Fixation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic

/-!
# Neutral heterozygosity path functionals

Expected sums of a function of gene frequency along sample paths are obtained from the
ordinary differential equation `L{Y(p)} + K(p) = 0`; under the boundary conditions
`Y(0) = Y(1) = 0` the solution is the Green formula. This functional programme is due to
T. Maruyama and M. Kimura, "Moments for Sum of an Arbitrary Function of Gene Frequency
along a Stochastic Path of Gene Frequency Change", Proc. Nat. Acad. Sci. USA 72(4),
1602-1604 (1975). These are the forward (until absorption) statements in diffusion units,
not their retrospective Eq. 21 and not a count in generations or individuals.

Conventions follow `Domains.Biology.PopulationGenetics.Diffusion.WrightFisher`: diploid
population of `N` individuals (`2N` gene copies), diffusion time in units of `2N`
generations, ideal population `N_e = N`, and the neutral backward generator `generator 0`
with coefficient `x (1 - x) / 2` on the second derivative. For `u(y) = 2y(1-y)` one has
`u(0) = u(1) = 0` and `generator 0 u = -u`, so the Green/Dynkin value from initial
frequency `x` is `2x(1-x)` in diffusion time units.

## Main results

* `generator_heterozygosity` (existing input): `generator 0 (fun z => 2z(1-z)) y = -(2y(1-y))`
  pointwise.
* `integral_two_mul_one_sub_absorptionTime`: for any neutral solution started at `x`, the
  stopped heterozygosity integral is integrable and its mean is `2x(1-x)`.
* `integral_two_mul_one_sub_absorptionTime_modifiedProcess`: the same identity for the
  constructed neutral realization `modifiedProcess x` under `rawMeasure x`.

## References

* T. Maruyama and M. Kimura, *Moments for Sum of an Arbitrary Function of Gene Frequency
  along a Stochastic Path of Gene Frequency Change*, Proc. Nat. Acad. Sci. USA 72(4),
  1602-1604 (1975), doi:10.1073/pnas.72.4.1602.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal unitInterval

open MathlibExt.Biology.PopulationGenetics.Diffusion (generator)
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
  (IsWrightFisherSolution absorptionTime)
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
  (modifiedProcess rawMeasure modifiedProcess_zero)
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
  (isWrightFisherSolution_one_sub isWrightFisherSolution_zero_modifiedProcess)

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

private theorem contDiff_heterozygosity :
    ContDiff ℝ 2 (fun y : ℝ => 2 * y * (1 - y)) :=
  ((contDiff_const (c := (2 : ℝ))).mul contDiff_id).mul
    ((contDiff_const (c := (1 : ℝ))).sub contDiff_id)

private theorem continuous_heterozygosity :
    Continuous fun y : ℝ => 2 * y * (1 - y) :=
  contDiff_heterozygosity.continuous

private theorem heterozygosity_mem_Icc {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ 2 * y * (1 - y) ∧ 2 * y * (1 - y) ≤ 1 / 2 := by
  obtain ⟨h1, h2⟩ := hy
  refine ⟨?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) h1) (by linarith)
  · nlinarith [sq_nonneg (y - 1 / 2), h1, h2]

private theorem measurable_apply {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {sig : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsWrightFisherSolution sig ℱ μ X) (t : ℝ≥0) :
    Measurable (X t) :=
  ((hX.2.2.1 t).mono (ℱ.le t)).measurable

private theorem integrable_heterozygosity_apply {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} {sig : ℝ} (hX : IsWrightFisherSolution sig ℱ μ X) (t : ℝ≥0) :
    Integrable (fun ω => 2 * X t ω * (1 - X t ω)) μ := by
  have hfm : AEStronglyMeasurable (fun ω => 2 * X t ω * (1 - X t ω)) μ :=
    (continuous_heterozygosity.measurable.comp (measurable_apply hX t)).aestronglyMeasurable
  refine Integrable.of_bound hfm (1 / 2) (ae_of_all _ fun ω => ?_)
  have h := heterozygosity_mem_Icc (hX.1 t ω)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

private theorem dynkin_heterozygosity {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) (t : ℝ≥0) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ∂μ =
        2 * x * (1 - x) - ∫ ω, 2 * X t ω * (1 - X t ω) ∂μ := by
  have hDyn := hX.integral_generator contDiff_heterozygosity t
  simp only [generator_heterozygosity, intervalIntegral.integral_neg, integral_neg] at hDyn
  have hE0 : ∫ ω, 2 * X 0 ω * (1 - X 0 ω) ∂μ = 2 * x * (1 - x) := by
    rw [integral_congr_ae (g := fun _ => 2 * x * (1 - x))
      (hX0.mono fun ω hω => by simp only [hω])]
    simp
  rw [hE0] at hDyn
  refine ⟨?_, ?_⟩
  · simpa using hDyn.1.neg
  · linarith [hDyn.2]

private theorem ae_stay_zero_neutral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X) :
    ∀ᵐ ω ∂μ, ∀ s t, s ≤ t → X s ω = 0 → X t ω = 0 :=
  MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess.ae_stay_zero_of_martingale
    (MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.martingale_of_neutral
      hX)
    (fun t ω => (hX.1 t ω).1) hX.2.1

private theorem ae_stay_one_neutral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X) :
    ∀ᵐ ω ∂μ, ∀ s t, s ≤ t → X s ω = 1 → X t ω = 1 := by
  filter_upwards [ae_stay_zero_neutral (isWrightFisherSolution_one_sub hX)] with ω h s t hst hs
  have hs0 : (1 : ℝ) - X s ω = 0 := by linarith [hs]
  have ht0 : (1 : ℝ) - X t ω = 0 := h s t hst hs0
  linarith [ht0]

private theorem integral_split_at_absorption {Y : ℝ≥0 → ℝ} (hY : Continuous Y)
    (_hmem : ∀ s, Y s ∈ Icc (0 : ℝ) 1) {τ : ℝ≥0}
    (hafter : ∀ s, τ ≤ s → Y s = 0 ∨ Y s = 1) {k : ℝ} (hk : (τ : ℝ) ≤ k) :
    (∫ s in (0 : ℝ)..k, 2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) =
      ∫ s in (0 : ℝ)..(τ : ℝ), 2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s)) := by
  have hcont : Continuous fun s : ℝ => 2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s)) :=
    (continuous_const.mul (hY.comp continuous_real_toNNReal)).mul
      (continuous_const.sub (hY.comp continuous_real_toNNReal))
  have htail : (∫ s in (τ : ℝ)..k, 2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    intro s hs
    rw [uIcc_of_le hk] at hs
    have hτs : τ ≤ Real.toNNReal s := by
      rw [Real.le_toNNReal_iff_coe_le ((τ.2).trans hs.1)]
      exact hs.1
    rcases hafter _ hτs with h0 | h1
    · simp [h0]
    · simp [h1]
  have hsplit : ((∫ s in (0 : ℝ)..(τ : ℝ), 2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) +
      ∫ s in (τ : ℝ)..k, 2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) =
      ∫ s in (0 : ℝ)..k, 2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s)) :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  rw [htail, add_zero] at hsplit
  exact hsplit.symm

/-- **Forward heterozygosity functional.** For a solution of the neutral Wright-Fisher
martingale problem started at frequency `x`, the expected heterozygosity accumulated until
absorption, in diffusion units (multiples of `2N` generations), is `2x(1-x)`. This is a
derived corollary of the Maruyama-Kimura functional machinery with `K = f`,
`f(y) = 2y(1-y)` and boundary values `0` at both endpoints, in the repository scaling. -/
theorem integral_two_mul_one_sub_absorptionTime {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ∂μ
        = 2 * x * (1 - x) := by
  have habs :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess.ae_exists_absorbed hX
  have hstay0 := ae_stay_zero_neutral hX
  have hstay1 := ae_stay_one_neutral hX
  have hafter : ∀ᵐ ω ∂μ, ∀ s : ℝ≥0, absorptionTime X ω ≤ s → X s ω = 0 ∨ X s ω = 1 := by
    filter_upwards [habs, hstay0, hstay1] with ω ⟨t₀, ht₀⟩ h0 h1
    have hcl : IsClosed {t | X t ω = 0 ∨ X t ω = 1} :=
      (isClosed_eq (hX.2.1 ω) continuous_const).union (isClosed_eq (hX.2.1 ω) continuous_const)
    have hne : {t | X t ω = 0 ∨ X t ω = 1}.Nonempty := by
      rcases ht₀ with h | h
      · exact ⟨t₀, Or.inl (h t₀ le_rfl)⟩
      · exact ⟨t₀, Or.inr (h t₀ le_rfl)⟩
    have hmem := hcl.csInf_mem hne (OrderBot.bddBelow _)
    intro s hs
    rcases hmem with h | h
    · exact Or.inl (h0 _ s hs h)
    · exact Or.inr (h1 _ s hs h)
  have hτint : Integrable (fun ω => (absorptionTime X ω : ℝ)) μ :=
    (MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess.integral_absorptionTime
      hX hX0).1
  have hD : ∀ k : ℕ, Integrable (fun ω => ∫ s in (0 : ℝ)..(k : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ∂μ =
        2 * x * (1 - x) - ∫ ω, 2 * X (k : ℝ≥0) ω * (1 - X (k : ℝ≥0) ω) ∂μ := by
    intro k
    have h := dynkin_heterozygosity hX hX0 (k : ℝ≥0)
    simpa only [NNReal.coe_natCast] using h
  have hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun k : ℕ => ∫ s in (0 : ℝ)..(k : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) atTop
      (nhds (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω))) := by
    filter_upwards [hafter] with ω hω
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop ⌈(absorptionTime X ω : ℝ)⌉₊] with k hk
    exact integral_split_at_absorption (hX.2.1 ω) (fun s => hX.1 s ω) hω
      ((Nat.le_ceil _).trans (by exact_mod_cast hk))
  have hball : ∀ᵐ ω ∂μ, ∀ k : ℕ, ‖∫ s in (0 : ℝ)..(k : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)‖ ≤
        (absorptionTime X ω : ℝ) := by
    filter_upwards [hafter] with ω hω k
    have hpt : ∀ s : ℝ, ‖2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)‖ ≤ 1 / 2 := by
      intro s
      have h := heterozygosity_mem_Icc (hX.1 (Real.toNNReal s) ω)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [h.1, h.2]
    by_cases hkτ : (k : ℝ) ≤ (absorptionTime X ω : ℝ)
    · refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (1 / 2 : ℝ)) fun s _ =>
        hpt s).trans ?_
      rw [sub_zero, abs_of_nonneg k.cast_nonneg]
      have hτ0 : (0 : ℝ) ≤ (absorptionTime X ω : ℝ) := NNReal.coe_nonneg _
      linarith [hkτ, hτ0]
    · have hkτ' := lt_of_not_ge hkτ
      have hsplit := integral_split_at_absorption (hX.2.1 ω) (fun s => hX.1 s ω) hω hkτ'.le
      rw [hsplit]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (1 / 2 : ℝ)) fun s _ =>
        hpt s).trans ?_
      rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
      have hτ0 : (0 : ℝ) ≤ (absorptionTime X ω : ℝ) := NNReal.coe_nonneg _
      linarith [hτ0]
  have hbound : ∀ k : ℕ, ∀ᵐ ω ∂μ, ‖∫ s in (0 : ℝ)..(k : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)‖ ≤
        (absorptionTime X ω : ℝ) :=
    fun k => hball.mono fun ω hω => hω k
  have hmean : Tendsto (fun k : ℕ => ∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ∂μ) atTop
      (nhds (∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => (absorptionTime X ω : ℝ))
      (fun k => (hD k).1.aestronglyMeasurable) hτint hbound hlim
  have hptbound : ∀ k : ℕ, ∀ᵐ ω ∂μ,
      ‖2 * X (k : ℝ≥0) ω * (1 - X (k : ℝ≥0) ω)‖ ≤ 1 / 2 :=
    fun k => ae_of_all _ fun ω => by
      have hb := heterozygosity_mem_Icc (hX.1 (k : ℝ≥0) ω)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hb.1, hb.2]
  have hEf0 : Tendsto (fun k : ℕ => ∫ ω, 2 * X (k : ℝ≥0) ω * (1 - X (k : ℝ≥0) ω) ∂μ)
      atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ => (1 / 2 : ℝ))
      (fun k => (integrable_heterozygosity_apply hX (k : ℝ≥0)).aestronglyMeasurable)
      (integrable_const _) hptbound (f := fun _ => (0 : ℝ)) ?_
    · simpa using h
    filter_upwards [habs] with ω ⟨t₀, ht₀⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈(t₀ : ℝ)⌉₊] with k hk
    have hk' : t₀ ≤ (k : ℝ≥0) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rcases ht₀ with h | h
    · simp [h _ hk']
    · simp [h _ hk']
  have key : ∀ k : ℕ, (∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ∂μ) =
        (2 * x * (1 - x)) - ∫ ω, 2 * X (k : ℝ≥0) ω * (1 - X (k : ℝ≥0) ω) ∂μ :=
    fun k => (hD k).2
  have hEq : Tendsto (fun k : ℕ => ∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ∂μ) atTop
      (nhds (2 * x * (1 - x))) := by
    have hconst : Tendsto (fun _ : ℕ => 2 * x * (1 - x)) atTop (nhds (2 * x * (1 - x))) :=
      tendsto_const_nhds
    have h : Tendsto
        (fun k : ℕ => 2 * x * (1 - x) - ∫ ω, 2 * X (k : ℝ≥0) ω * (1 - X (k : ℝ≥0) ω) ∂μ)
        atTop (nhds (2 * x * (1 - x) - 0)) :=
      Filter.Tendsto.sub hconst hEf0
    rw [sub_zero] at h
    exact (tendsto_congr' (Eventually.of_forall fun k => key k)).mpr h
  have hval := tendsto_nhds_unique hmean hEq
  have hFm : AEStronglyMeasurable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) μ := by
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hD k).1.aestronglyMeasurable) hlim
  have hFbound : ∀ᵐ ω ∂μ, ‖∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)‖ ≤
      (absorptionTime X ω : ℝ) := by
    refine ae_of_all _ fun ω => ?_
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (1 / 2 : ℝ))
      fun s _ => ?_).trans
      ?_
    · have h := heterozygosity_mem_Icc (hX.1 (Real.toNNReal s) ω)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [h.1, h.2]
    · rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
      have hτ0 : (0 : ℝ) ≤ (absorptionTime X ω : ℝ) := NNReal.coe_nonneg _
      linarith [hτ0]
  have hFint : Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) μ :=
    hτint.mono' hFm hFbound
  exact ⟨hFint, hval⟩

/-- **Realization reading.** For every `x : I`, the stopped heterozygosity integral of the
constructed neutral realization `modifiedProcess x` is integrable with respect to
`rawMeasure x`, and its integral equals `2x(1-x)`. This is the non-vacuity reading of
`integral_two_mul_one_sub_absorptionTime` for the realization identified by
`isWrightFisherSolution_zero_modifiedProcess`. -/
theorem integral_two_mul_one_sub_absorptionTime_modifiedProcess (x : I) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
        2 * modifiedProcess x (Real.toNNReal s) ω *
          (1 - modifiedProcess x (Real.toNNReal s) ω)) (rawMeasure x) ∧
      ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
        2 * modifiedProcess x (Real.toNNReal s) ω *
          (1 - modifiedProcess x (Real.toNNReal s) ω)) ∂(rawMeasure x)
        = 2 * (x : ℝ) * (1 - (x : ℝ)) := by
  exact integral_two_mul_one_sub_absorptionTime
    (isWrightFisherSolution_zero_modifiedProcess x)
    (ae_of_all _ fun ω => modifiedProcess_zero x ω)

end MathlibExt.Biology.PopulationGenetics.Diffusion
