/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.PathFunctionals
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Stability of stopped occupation under uniform limits

For the neutral Wright-Fisher diffusion, potentials arising from Green kernels solve
`L₀ u = -g` on `(0, 1)` with zero boundary values, but are typically not twice
continuously differentiable on all of `ℝ`, so the general stopped-occupation identity
(`integral_absorptionTime_of_generator_eq_neg`) does not apply to them directly. This
module proves that the identity persists under uniform approximation on `[0, 1]`: if
smooth potentials `uₙ` with integrands `gₙ` satisfy the general hypotheses for each `n`,
and `uₙ → u` and `gₙ → g` uniformly on the closed unit interval, then the stopped
occupation of the limit integrand `g` is integrable with expectation `u x`. The limit
step is dominated convergence with dominator a constant times the absorption time.

## Conventions

* Uniform convergence is `TendstoUniformlyOn` on `Set.Icc 0 1` with `Filter.atTop`.
* Integral shapes and binders mirror `integral_absorptionTime_of_generator_eq_neg`.
* The starting point `x` must lie in `Set.Icc 0 1`: each approximant is globally smooth
  so the general theorem gives `uₙ x` for arbitrary real `x`, while uniform convergence
  on `[0, 1]` controls the limit only there.
* The hypotheses are non-vacuous: constant sequences reduce to the general theorem.

## Non-goals

This is a stability/closure statement only. It does not claim that any particular Green
potential is approximable in this sense, states no occupation-density (local-time)
identity, and does not extend to nonzero selection.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*,
  John Wiley & Sons, 1986, Chapter 4 (martingale-problem Dynkin identity).
* T. Maruyama and M. Kimura (1975), in the neutral-diffusion lineage of the
  path-functional module; see that module for the full citation.
-/

open MeasureTheory Filter Set
open scoped NNReal unitInterval BigOperators ENNReal
open MathlibExt.Biology.PopulationGenetics.Diffusion (generator)
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem

@[expose] public section
namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Stability of the neutral stopped-occupation identity under uniform limits.

If smooth potentials `u n` with integrands `g n` satisfy the hypotheses of
`integral_absorptionTime_of_generator_eq_neg` for every `n`, and converge uniformly on
`Set.Icc 0 1` to `uInf` and `gInf`, then the stopped occupation of `gInf` is integrable
and its expectation is `uInf x`, for starting points `x` in `[0, 1]`.

The `x ∈ Set.Icc 0 1` hypothesis is included explicitly for readability, since uniform
convergence on `[0, 1]` controls the limit only there; it in fact follows from the
range condition and the almost-everywhere initial condition, since the measure is a
probability measure.

This is a closure statement only: it assumes approximants and uniform convergence, and
claims nothing about approximability of any particular Green potential, no
occupation-density identity, and no nonzero selection. -/
theorem integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ}
    (hX : IsWrightFisherSolution 0 ℱ μ X) (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x)
    {u g : ℕ → ℝ → ℝ} {uInf gInf : ℝ → ℝ}
    (hu : ∀ n, ContDiff ℝ 2 (u n)) (hg : ∀ n, Continuous (g n))
    (hgen : ∀ n y, generator 0 (u n) y = -g n y)
    (hu0 : ∀ n, u n 0 = 0) (hu1 : ∀ n, u n 1 = 0)
    (hgInf : Continuous gInf)
    (hunif : TendstoUniformlyOn u uInf atTop (Set.Icc 0 1))
    (hgunif : TendstoUniformlyOn g gInf atTop (Set.Icc 0 1))
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      gInf (X (Real.toNNReal s) ω)) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        gInf (X (Real.toNNReal s) ω)) ∂μ = uInf x := by
  -- Each approximant satisfies the general stopped-occupation identity.
  have hOcc : ∀ n : ℕ, Integrable
      (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        g n (X (Real.toNNReal s) ω)) μ ∧
      (∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        g n (X (Real.toNNReal s) ω)) ∂μ) = u n x := fun n =>
    integral_absorptionTime_of_generator_eq_neg hX hX0 (hu n) (hg n)
      (hgen n) (hu0 n) (hu1 n)
  -- Uniform convergence gives an eventual uniform bound on `[0, 1]`.
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hgunif) 1 one_pos)
  -- The continuous limit is bounded on the compact interval.
  obtain ⟨M, _hMmem, hM⟩ := IsCompact.exists_isMaxOn isCompact_Icc
    (Set.nonempty_Icc.mpr zero_le_one) (hgInf.continuousOn.abs)
  -- Each approximant is bounded on the compact interval.
  have hbound : ∀ n : ℕ, ∃ C : ℝ,
      ∀ y ∈ Set.Icc (0 : ℝ) 1, |g n y| ≤ C := by
    intro n
    obtain ⟨Mn, _hMnmem, hMn⟩ := IsCompact.exists_isMaxOn isCompact_Icc
      (Set.nonempty_Icc.mpr zero_le_one) ((hg n).continuousOn.abs)
    exact ⟨|g n Mn|, fun y hy => hMn hy⟩
  choose C hC using hbound
  -- Overall bound combining the eventual bound and the finite head.
  have hB : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Icc (0 : ℝ) 1 →
      |g n y| ≤ (|gInf M| + 1) +
        ∑ k ∈ Finset.range (N + 1), (|C k| + 1) := by
    intro n y hy
    by_cases hn : n ≥ N
    · have hdist := hN n hn y hy
      rw [dist_comm, Real.dist_eq] at hdist
      have heq : g n y = gInf y + (g n y - gInf y) := by ring
      have h2 : |g n y| ≤ |gInf y| + 1 := by
        rw [heq]
        exact le_trans (abs_add_le _ _) (by linarith [hdist])
      have h3 : |gInf y| ≤ |gInf M| := hM hy
      have hsum : (0 : ℝ) ≤ ∑ k ∈ Finset.range (N + 1), (|C k| + 1) :=
        Finset.sum_nonneg (fun k _ => by positivity)
      calc |g n y| ≤ |gInf y| + 1 := h2
        _ ≤ |gInf M| + 1 := by linarith [h3]
        _ ≤ (|gInf M| + 1) + ∑ k ∈ Finset.range (N + 1), (|C k| + 1) :=
          le_add_of_nonneg_right hsum
    · push Not at hn
      have hnmem : n ∈ Finset.range (N + 1) :=
        Finset.mem_range.mpr (by omega)
      have hterm : |C n| + 1 ≤
          ∑ k ∈ Finset.range (N + 1), (|C k| + 1) :=
        Finset.single_le_sum (f := fun k : ℕ => (|C k| + 1 : ℝ))
          (fun k _ => by positivity) hnmem
      have hnC : |g n y| ≤ C n := hC n y hy
      have hCn : C n ≤ |C n| + 1 :=
        le_trans (le_abs_self _) (le_add_of_nonneg_right zero_le_one)
      have hnn : (0 : ℝ) ≤ |gInf M| + 1 := by positivity
      calc |g n y| ≤ C n := hnC
        _ ≤ |C n| + 1 := hCn
        _ ≤ ∑ k ∈ Finset.range (N + 1), (|C k| + 1) := hterm
        _ ≤ (|gInf M| + 1) + ∑ k ∈ Finset.range (N + 1), (|C k| + 1) :=
          le_add_of_nonneg_left hnn
  -- The solution stays in `[0, 1]` and has continuous paths.
  have hmem : ∀ (t : ℝ≥0) (ω : Ω), X t ω ∈ Set.Icc (0 : ℝ) 1 :=
    hX.1
  have hcont : ∀ ω : Ω, Continuous (fun t : ℝ≥0 => X t ω) :=
    hX.2.1
  have hNN : Continuous Real.toNNReal :=
    Continuous.subtype_mk (continuous_id.max continuous_const)
      (fun x => le_max_right x 0)
  -- Inner integrands are integrable on compact time intervals.
  have hinner : ∀ (n : ℕ) (ω : Ω) (τ : ℝ),
      IntegrableOn (fun s : ℝ => g n (X (Real.toNNReal s) ω))
        (Set.Icc 0 τ) volume :=
    fun n ω τ =>
      (((hg n).comp ((hcont ω).comp hNN)).continuousOn).integrableOn_compact
        isCompact_Icc
  have hinnerInf : ∀ (ω : Ω) (τ : ℝ),
      IntegrableOn (fun s : ℝ => gInf (X (Real.toNNReal s) ω))
        (Set.Icc 0 τ) volume :=
    fun ω τ =>
      ((hgInf.comp ((hcont ω).comp hNN)).continuousOn).integrableOn_compact
        isCompact_Icc
  -- Absorption times are nonnegative.
  have hτ0 : ∀ ω : Ω, (0 : ℝ) ≤ (absorptionTime X ω : ℝ) := fun ω => by
    positivity
  -- The mean-absorption identity makes the dominator integrable.
  have hτint : Integrable (fun ω : Ω => (absorptionTime X ω : ℝ)) μ :=
    (KimuraFixationProcess.integral_absorptionTime hX hX0).1
  have hBoundInt : Integrable
      (fun ω : Ω => ((|gInf M| + 1) +
        ∑ k ∈ Finset.range (N + 1), (|C k| + 1)) *
        (absorptionTime X ω : ℝ)) μ :=
    hτint.const_mul _
  -- Each occupation is dominated by `B * τ`, everywhere.
  have hBound : ∀ (n : ℕ) (ω : Ω),
      ‖∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        g n (X (Real.toNNReal s) ω)‖ ≤
        ((|gInf M| + 1) +
          ∑ k ∈ Finset.range (N + 1), (|C k| + 1)) *
          (absorptionTime X ω : ℝ) := by
    intro n ω
    rw [intervalIntegral.integral_of_le (hτ0 ω)]
    have hsIoc : volume (Set.Ioc 0 (absorptionTime X ω : ℝ)) < ∞ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    have hbdd : ∀ᵐ s ∂(volume.restrict
        (Set.Ioc 0 (absorptionTime X ω : ℝ))),
        ‖g n (X (Real.toNNReal s) ω)‖ ≤ (|gInf M| + 1) +
          ∑ k ∈ Finset.range (N + 1), (|C k| + 1) :=
      Eventually.of_forall (fun s => by
        have hmem' : X (Real.toNNReal s) ω ∈ Set.Icc (0 : ℝ) 1 :=
          hmem (Real.toNNReal s) ω
        rw [Real.norm_eq_abs]
        exact hB n _ hmem')
    have hle := norm_setIntegral_le_of_norm_le_const_ae hsIoc hbdd
    have hτ0' : (0 : ℝ) ≤ (absorptionTime X ω : ℝ) - 0 := by
      linarith [hτ0 ω]
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hτ0'] at hle
    simpa using hle
  -- Occupations converge pointwise, everywhere.
  have hlim : ∀ ω : Ω, Tendsto
      (fun n : ℕ => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        g n (X (Real.toNNReal s) ω)) atTop
      (nhds (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        gInf (X (Real.toNNReal s) ω))) := by
    intro ω
    rw [Metric.tendsto_nhds]
    intro ε hε
    set ε' : ℝ := ε / ((absorptionTime X ω : ℝ) + 1) with hε'
    have hε'0 : 0 < ε' := by
      rw [hε']
      exact div_pos hε (by linarith [hτ0 ω])
    have hunif' := (Metric.tendstoUniformlyOn_iff.mp hgunif) ε' hε'0
    filter_upwards [hunif'] with n hn
    simp only [Real.dist_eq]
    have hIn : IntegrableOn (fun s : ℝ => g n (X (Real.toNNReal s) ω))
        (Set.Ioc 0 (absorptionTime X ω : ℝ)) volume :=
      (hinner n ω _).mono_set Set.Ioc_subset_Icc_self
    have hIinf : IntegrableOn (fun s : ℝ => gInf (X (Real.toNNReal s) ω))
        (Set.Ioc 0 (absorptionTime X ω : ℝ)) volume :=
      (hinnerInf ω _).mono_set Set.Ioc_subset_Icc_self
    have hsub : (∫ s in Set.Ioc 0 (absorptionTime X ω : ℝ),
          (g n (X (Real.toNNReal s) ω) -
            gInf (X (Real.toNNReal s) ω)) ∂volume) =
        (∫ s in Set.Ioc 0 (absorptionTime X ω : ℝ),
          g n (X (Real.toNNReal s) ω) ∂volume) -
        (∫ s in Set.Ioc 0 (absorptionTime X ω : ℝ),
          gInf (X (Real.toNNReal s) ω) ∂volume) :=
      integral_sub hIn hIinf
    have hbdd' : ∀ᵐ s ∂(volume.restrict
        (Set.Ioc 0 (absorptionTime X ω : ℝ))),
        ‖g n (X (Real.toNNReal s) ω) -
          gInf (X (Real.toNNReal s) ω)‖ ≤ ε' :=
      Eventually.of_forall (fun s => by
        have hmem' : X (Real.toNNReal s) ω ∈ Set.Icc (0 : ℝ) 1 :=
          hmem (Real.toNNReal s) ω
        have hdist := hn _ hmem'
        rw [dist_comm] at hdist
        rw [Real.norm_eq_abs, ← Real.dist_eq]
        exact le_of_lt hdist)
    have hsIoc' : volume (Set.Ioc 0 (absorptionTime X ω : ℝ)) < ∞ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    have hle' := norm_setIntegral_le_of_norm_le_const_ae hsIoc' hbdd'
    have hτ0'' : (0 : ℝ) ≤ (absorptionTime X ω : ℝ) - 0 := by
      linarith [hτ0 ω]
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hτ0''] at hle'
    rw [Real.norm_eq_abs] at hle'
    rw [intervalIntegral.integral_of_le (hτ0 ω),
      intervalIntegral.integral_of_le (hτ0 ω), ← hsub]
    have hτ1ne : (absorptionTime X ω : ℝ) + 1 ≠ 0 := ne_of_gt (by
      linarith [hτ0 ω])
    have hcancel : ε' * ((absorptionTime X ω : ℝ) + 1) = ε := by
      rw [hε']
      field_simp [hτ1ne]
    have hlt : ε' * (absorptionTime X ω : ℝ) <
        ε' * ((absorptionTime X ω : ℝ) + 1) :=
      mul_lt_mul_of_pos_left (lt_add_one _) hε'0
    rw [hcancel] at hlt
    have hfin : ε' * ((absorptionTime X ω : ℝ) - 0) < ε := by
      rw [sub_zero]
      exact hlt
    exact lt_of_le_of_lt hle' hfin
  -- Dominated convergence for the approximant means.
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω : Ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        g n (X (Real.toNNReal s) ω)) μ :=
    fun n => (hOcc n).1.aestronglyMeasurable
  have hBoundAE : ∀ n : ℕ, ∀ᵐ ω ∂μ,
      ‖∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        g n (X (Real.toNNReal s) ω)‖ ≤
        ((|gInf M| + 1) +
          ∑ k ∈ Finset.range (N + 1), (|C k| + 1)) *
          (absorptionTime X ω : ℝ) :=
    fun n => Eventually.of_forall (hBound n)
  have hlimAE : ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        g n (X (Real.toNNReal s) ω)) atTop
      (nhds (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        gInf (X (Real.toNNReal s) ω))) :=
    Eventually.of_forall hlim
  have hDCT := tendsto_integral_of_dominated_convergence _ hFmeas hBoundInt
    hBoundAE hlimAE
  -- The approximant means converge to the limit value.
  have hEq : ∀ n : ℕ, (∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      g n (X (Real.toNNReal s) ω)) ∂μ) = u n x :=
    fun n => (hOcc n).2
  have hu_lim : Tendsto (fun n : ℕ => u n x) atTop (nhds (uInf x)) :=
    hunif.tendsto_at hx
  have hDCT' : Tendsto (fun n : ℕ => u n x) atTop
      (nhds (∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        gInf (X (Real.toNNReal s) ω)) ∂μ)) := by
    simpa only [hEq] using hDCT
  -- The limit occupation is integrable.
  have hIntLim : Integrable
      (fun ω : Ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        gInf (X (Real.toNNReal s) ω)) μ := by
    have hmeas : AEStronglyMeasurable
        (fun ω : Ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
          gInf (X (Real.toNNReal s) ω)) μ :=
      aestronglyMeasurable_of_tendsto_ae atTop hFmeas hlimAE
    have hlimBound : ∀ᵐ ω ∂μ, ‖∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
          gInf (X (Real.toNNReal s) ω)‖ ≤
        ((|gInf M| + 1) +
          ∑ k ∈ Finset.range (N + 1), (|C k| + 1)) *
          (absorptionTime X ω : ℝ) := by
      filter_upwards [hlimAE] with ω hω
      exact le_of_tendsto hω.norm (Eventually.of_forall fun n => hBound n ω)
    exact hBoundInt.mono' hmeas hlimBound
  exact ⟨hIntLim, tendsto_nhds_unique hDCT' hu_lim⟩

/-- Realization companion of `integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn`.

Same stability statement for `modifiedProcess x` under `rawMeasure x`, with value
`uInf ↑x`. Since `x : I` already lies in the unit interval, no separate membership
hypothesis is needed. Same conventions and non-goals as the main stability theorem. -/
theorem integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn_modifiedProcess
    (x : I) {u g : ℕ → ℝ → ℝ} {uInf gInf : ℝ → ℝ}
    (hu : ∀ n, ContDiff ℝ 2 (u n)) (hg : ∀ n, Continuous (g n))
    (hgen : ∀ n y, generator 0 (u n) y = -g n y)
    (hu0 : ∀ n, u n 0 = 0) (hu1 : ∀ n, u n 1 = 0)
    (hgInf : Continuous gInf)
    (hunif : TendstoUniformlyOn u uInf atTop (Set.Icc 0 1))
    (hgunif : TendstoUniformlyOn g gInf atTop (Set.Icc 0 1)) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
      gInf ((modifiedProcess x) (Real.toNNReal s) ω)) (rawMeasure x) ∧
      ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
        gInf ((modifiedProcess x) (Real.toNNReal s) ω)) ∂(rawMeasure x) = uInf ↑x := by
  exact integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn
    (isWrightFisherSolution_zero_modifiedProcess x)
    (ae_of_all _ fun ω => modifiedProcess_zero x ω)
    hu hg hgen hu0 hu1 hgInf hunif hgunif x.2

end MathlibExt.Biology.PopulationGenetics.Diffusion
