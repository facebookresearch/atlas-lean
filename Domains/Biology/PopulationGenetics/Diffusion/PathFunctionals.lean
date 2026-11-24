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
* `integral_absorptionTime_of_generator_eq_neg`: for any neutral solution started at `x`,
  a continuous test function `g` and a `C²` potential `u` with `generator 0 u = -g` and
  `u(0) = u(1) = 0`, the stopped occupation integral of `g` is integrable with mean `u x`.
* `integral_absorptionTime_of_generator_eq_neg_modifiedProcess`: the same identity for the
  constructed neutral realization `modifiedProcess x` under `rawMeasure x`.
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

private theorem generator_neutral_endpoints {u : ℝ → ℝ} :
    generator 0 u 0 = 0 ∧ generator 0 u 1 = 0 := by
  simp only [generator]
  norm_num

private theorem measurable_apply {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {sig : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsWrightFisherSolution sig ℱ μ X) (t : ℝ≥0) :
    Measurable (X t) :=
  ((hX.2.2.1 t).mono (ℱ.le t)).measurable

private theorem integrable_apply {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} {sig : ℝ} (hX : IsWrightFisherSolution sig ℱ μ X)
    {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ≥0) :
    Integrable (fun ω => f (X t ω)) μ := by
  obtain ⟨B, hB⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc (0 : ℝ) 1))
  have hfm : AEStronglyMeasurable (fun ω => f (X t ω)) μ :=
    (hf.measurable.comp (measurable_apply hX t)).aestronglyMeasurable
  exact Integrable.of_bound hfm B (ae_of_all _ fun ω => hB _ (hX.1 t ω))

private theorem dynkin_of_generator_eq_neg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) {u g : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hgen : ∀ y, generator 0 u y = -g y) (t : ℝ≥0) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ),
        g (X (Real.toNNReal s) ω)) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ),
        g (X (Real.toNNReal s) ω)) ∂μ =
        u x - ∫ ω, u (X t ω) ∂μ := by
  have hDyn := hX.integral_generator hu t
  simp only [hgen, intervalIntegral.integral_neg, integral_neg] at hDyn
  have hE0 : ∫ ω, u (X 0 ω) ∂μ = u x := by
    rw [integral_congr_ae (g := fun _ => u x)
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
  hX.ae_stay_zero

private theorem ae_stay_one_neutral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X) :
    ∀ᵐ ω ∂μ, ∀ s t, s ≤ t → X s ω = 1 → X t ω = 1 :=
  hX.ae_stay_one

private theorem integral_split_at_absorption {g : ℝ → ℝ} (hg : Continuous g)
    {Y : ℝ≥0 → ℝ} (hY : Continuous Y)
    (_hmem : ∀ s, Y s ∈ Icc (0 : ℝ) 1) {τ : ℝ≥0}
    (hafter : ∀ s, τ ≤ s → Y s = 0 ∨ Y s = 1) (hg0 : g 0 = 0) (hg1 : g 1 = 0)
    {k : ℝ} (hk : (τ : ℝ) ≤ k) :
    (∫ s in (0 : ℝ)..k, g (Y (Real.toNNReal s))) =
      ∫ s in (0 : ℝ)..(τ : ℝ), g (Y (Real.toNNReal s)) := by
  have hcont : Continuous fun s : ℝ => g (Y (Real.toNNReal s)) :=
    hg.comp (hY.comp continuous_real_toNNReal)
  have htail : (∫ s in (τ : ℝ)..k, g (Y (Real.toNNReal s))) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    intro s hs
    rw [uIcc_of_le hk] at hs
    have hτs : τ ≤ Real.toNNReal s := by
      rw [Real.le_toNNReal_iff_coe_le ((τ.2).trans hs.1)]
      exact hs.1
    rcases hafter _ hτs with h0 | h1
    · simp [h0, hg0]
    · simp [h1, hg1]
  have hsplit : ((∫ s in (0 : ℝ)..(τ : ℝ), g (Y (Real.toNNReal s))) +
      ∫ s in (τ : ℝ)..k, g (Y (Real.toNNReal s))) =
      ∫ s in (0 : ℝ)..k, g (Y (Real.toNNReal s)) :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  rw [htail, add_zero] at hsplit
  exact hsplit.symm

/-- **Forward occupation functional.** For a solution of the neutral Wright-Fisher martingale
problem started at frequency `x` under a probability measure, a continuous test function `g` with
`C²` potential `u` satisfying `generator 0 u = -g` and `u(0) = u(1) = 0`, the forward occupation
integral of `g` accumulated until absorption is integrable, and its expectation, in diffusion units
(multiples of `2N` generations), is `u x`. This is the Maruyama-Kimura functional programme with
`K = g` and boundary values `0` at both endpoints, in the repository scaling. -/
theorem integral_absorptionTime_of_generator_eq_neg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) {u g : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hg : Continuous g)
    (hgen : ∀ y, generator 0 u y = -g y) (hu0 : u 0 = 0) (hu1 : u 1 = 0) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        g (X (Real.toNNReal s) ω)) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ), g (X (Real.toNNReal s) ω)) ∂μ
        = u x := by
  have hgen0 := (generator_neutral_endpoints (u := u)).1
  have hgen1 := (generator_neutral_endpoints (u := u)).2
  have hg0 : g 0 = 0 := by linarith [hgen 0, hgen0]
  have hg1 : g 1 = 0 := by linarith [hgen 1, hgen1]
  obtain ⟨Bg, hBg⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨Bu, hBu⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn
      (hu.continuous.continuousOn (s := Icc (0 : ℝ) 1))
  have hgB : ∀ y ∈ Icc (0 : ℝ) 1, ‖g y‖ ≤ |Bg| := fun y hy => (hBg y hy).trans (le_abs_self _)
  have huB : ∀ y ∈ Icc (0 : ℝ) 1, ‖u y‖ ≤ |Bu| := fun y hy => (hBu y hy).trans (le_abs_self _)
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
  have hτB : Integrable (fun ω => |Bg| * (absorptionTime X ω : ℝ)) μ :=
    hτint.const_mul |Bg|
  have hD : ∀ k : ℕ, Integrable (fun ω => ∫ s in (0 : ℝ)..(k : ℝ),
        g (X (Real.toNNReal s) ω)) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        g (X (Real.toNNReal s) ω)) ∂μ =
        u x - ∫ ω, u (X (k : ℝ≥0) ω) ∂μ := by
    intro k
    have h := dynkin_of_generator_eq_neg hX hX0 hu hgen (k : ℝ≥0)
    simpa only [NNReal.coe_natCast] using h
  have hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun k : ℕ => ∫ s in (0 : ℝ)..(k : ℝ),
        g (X (Real.toNNReal s) ω)) atTop
      (nhds (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        g (X (Real.toNNReal s) ω))) := by
    filter_upwards [hafter] with ω hω
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop ⌈(absorptionTime X ω : ℝ)⌉₊] with k hk
    exact integral_split_at_absorption hg (hX.2.1 ω) (fun s => hX.1 s ω) hω hg0 hg1
      ((Nat.le_ceil _).trans (by exact_mod_cast hk))
  have hB0 : (0 : ℝ) ≤ |Bg| := abs_nonneg _
  have hball : ∀ᵐ ω ∂μ, ∀ k : ℕ, ‖∫ s in (0 : ℝ)..(k : ℝ),
        g (X (Real.toNNReal s) ω)‖ ≤ |Bg| * (absorptionTime X ω : ℝ) := by
    filter_upwards [hafter] with ω hω k
    have hpt : ∀ s : ℝ, ‖g (X (Real.toNNReal s) ω)‖ ≤ |Bg| := by
      intro s
      exact hgB _ (hX.1 (Real.toNNReal s) ω)
    by_cases hkτ : (k : ℝ) ≤ (absorptionTime X ω : ℝ)
    · refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := |Bg|) fun s _ =>
        hpt s).trans ?_
      have hk0 : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg k.cast_nonneg
      rw [sub_zero, hk0]
      have hle : |Bg| * (k : ℝ) ≤ |Bg| * (absorptionTime X ω : ℝ) :=
        mul_le_mul_of_nonneg_left hkτ hB0
      linarith [hle]
    · have hkτ' := lt_of_not_ge hkτ
      have hsplit := integral_split_at_absorption hg (hX.2.1 ω) (fun s => hX.1 s ω) hω hg0 hg1
        hkτ'.le
      rw [hsplit]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := |Bg|) fun s _ =>
        hpt s).trans ?_
      have hτabs : |(absorptionTime X ω : ℝ)| = (absorptionTime X ω : ℝ) :=
        abs_of_nonneg (NNReal.coe_nonneg _)
      rw [sub_zero, hτabs]
  have hbound : ∀ k : ℕ, ∀ᵐ ω ∂μ, ‖∫ s in (0 : ℝ)..(k : ℝ),
        g (X (Real.toNNReal s) ω)‖ ≤ |Bg| * (absorptionTime X ω : ℝ) :=
    fun k => hball.mono fun ω hω => hω k
  have hmean : Tendsto (fun k : ℕ => ∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        g (X (Real.toNNReal s) ω)) ∂μ) atTop
      (nhds (∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        g (X (Real.toNNReal s) ω)) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => |Bg| * (absorptionTime X ω : ℝ))
      (fun k => (hD k).1.aestronglyMeasurable) hτB hbound hlim
  have hptbound : ∀ k : ℕ, ∀ᵐ ω ∂μ,
      ‖u (X (k : ℝ≥0) ω)‖ ≤ |Bu| :=
    fun k => ae_of_all _ fun ω => huB _ (hX.1 (k : ℝ≥0) ω)
  have hEf0 : Tendsto (fun k : ℕ => ∫ ω, u (X (k : ℝ≥0) ω) ∂μ)
      atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ => |Bu|)
      (fun k => (integrable_apply hX hu.continuous (k : ℝ≥0)).aestronglyMeasurable)
      (integrable_const _) hptbound (f := fun _ => (0 : ℝ)) ?_
    · simpa using h
    filter_upwards [habs] with ω ⟨t₀, ht₀⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈(t₀ : ℝ)⌉₊] with k hk
    have hk' : t₀ ≤ (k : ℝ≥0) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rcases ht₀ with h | h
    · simp [h _ hk', hu0]
    · simp [h _ hk', hu1]
  have key : ∀ k : ℕ, (∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        g (X (Real.toNNReal s) ω)) ∂μ) =
        u x - ∫ ω, u (X (k : ℝ≥0) ω) ∂μ :=
    fun k => (hD k).2
  have hEq : Tendsto (fun k : ℕ => ∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        g (X (Real.toNNReal s) ω)) ∂μ) atTop
      (nhds (u x)) := by
    have hconst : Tendsto (fun _ : ℕ => u x) atTop (nhds (u x)) :=
      tendsto_const_nhds
    have h : Tendsto
        (fun k : ℕ => u x - ∫ ω, u (X (k : ℝ≥0) ω) ∂μ)
        atTop (nhds (u x - 0)) :=
      Filter.Tendsto.sub hconst hEf0
    rw [sub_zero] at h
    exact (tendsto_congr' (Eventually.of_forall fun k => key k)).mpr h
  have hval := tendsto_nhds_unique hmean hEq
  have hFm : AEStronglyMeasurable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      g (X (Real.toNNReal s) ω)) μ := by
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hD k).1.aestronglyMeasurable) hlim
  have hFbound : ∀ᵐ ω ∂μ, ‖∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      g (X (Real.toNNReal s) ω)‖ ≤ |Bg| * (absorptionTime X ω : ℝ) := by
    refine ae_of_all _ fun ω => ?_
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := |Bg|)
      fun s _ => ?_).trans
      ?_
    · exact hgB _ (hX.1 (Real.toNNReal s) ω)
    · have hτabs : |(absorptionTime X ω : ℝ)| = (absorptionTime X ω : ℝ) :=
        abs_of_nonneg (NNReal.coe_nonneg _)
      rw [sub_zero, hτabs]
  have hFint : Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      g (X (Real.toNNReal s) ω)) μ :=
    hτB.mono' hFm hFbound
  exact ⟨hFint, hval⟩

/-- **Realization reading.** For every `x : I`, a continuous test function `g` with `C²`
potential `u` satisfying `generator 0 u = -g` and `u(0) = u(1) = 0`, the stopped
occupation integral of `g` along the constructed neutral realization `modifiedProcess x`
is integrable with respect to `rawMeasure x`, and its integral equals `u x`. This is the
non-vacuity reading, in diffusion time units, of the Maruyama-Kimura forward occupation
functional `integral_absorptionTime_of_generator_eq_neg` for the realization identified
by `isWrightFisherSolution_zero_modifiedProcess`. -/
theorem integral_absorptionTime_of_generator_eq_neg_modifiedProcess (x : I) {u g : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hg : Continuous g)
    (hgen : ∀ y, generator 0 u y = -g y) (hu0 : u 0 = 0) (hu1 : u 1 = 0) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
        g (modifiedProcess x (Real.toNNReal s) ω)) (rawMeasure x) ∧
      ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
        g (modifiedProcess x (Real.toNNReal s) ω)) ∂(rawMeasure x)
        = u (x : ℝ) := by
  exact integral_absorptionTime_of_generator_eq_neg
    (isWrightFisherSolution_zero_modifiedProcess x)
    (ae_of_all _ fun ω => modifiedProcess_zero x ω) hu hg hgen hu0 hu1

/-- **Forward heterozygosity functional.** For a solution of the neutral Wright-Fisher martingale
problem started at frequency `x` under a probability measure, the heterozygosity accumulated until
absorption is integrable, and its expectation, in diffusion units (multiples of `2N` generations),
is `2x(1-x)`. This is a derived corollary of the Maruyama-Kimura functional machinery with `K = f`,
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
  have h0 : (fun y : ℝ => 2 * y * (1 - y)) 0 = 0 := by simp
  have h1 : (fun y : ℝ => 2 * y * (1 - y)) 1 = 0 := by simp
  exact integral_absorptionTime_of_generator_eq_neg hX hX0 contDiff_heterozygosity
    continuous_heterozygosity generator_heterozygosity h0 h1

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
  have h0 : (fun y : ℝ => 2 * y * (1 - y)) 0 = 0 := by simp
  have h1 : (fun y : ℝ => 2 * y * (1 - y)) 1 = 0 := by simp
  exact integral_absorptionTime_of_generator_eq_neg_modifiedProcess x
    contDiff_heterozygosity continuous_heterozygosity generator_heterozygosity h0 h1

end MathlibExt.Biology.PopulationGenetics.Diffusion
