/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Optional stopping for uniformly integrable martingales

For a uniformly integrable martingale `f` and an *arbitrary* stopping time
`τ` (possibly infinite), stopping preserves expectation:
`∫ f 0 = ∫ f_τ = ∫ f_∞`, where `f_∞` is the a.e. limit of `f` and `f_τ`
is `f` evaluated at `τ`, with the limit `f_∞` used on `{τ = ∞}`.
In particular the stopped process `n ↦ f_{τ ∧ n}` is uniformly integrable.

## Source

This proves the martingale cases of the targets
"Theorem (General optional stopping, uniform integrability preservation)"
and "Theorem (General optional stopping, expectation inequality)"
(Lecture 29) of `v1/Atlas/TheoryOfProbability/targets.yaml`:

* "Let `X_n` be a uniformly integrable submartingale; for any stopping
  time `N ≤ ∞` we have `EX_0 ≤ EX_N ≤ EX_∞`."

For martingales, the expectation inequalities sharpen to equalities.
The separate target "Theorem (General form of optional stopping)"
concerns arbitrary stopping times `L ≤ M`, assumes uniform integrability
of `Y_{M ∧ n}`, and concludes both `EY_L ≤ EY_M` and
`Y_L ≤ E(Y_M | ℱ_L)`. That general conditional target is omitted here.

The v1 expectation statement is
`v1/Atlas/TheoryOfProbability/code/GeneralOptionalStopping.lean`
(`general_optional_stopping`, left unproved). UI preservation is stated in
`v1/Atlas/TheoryOfProbability/code/OptionalStoppingUI.lean`
(`optional_stopping_uniformly_integrable`), whose helper in
`v1/Atlas/TheoryOfProbability/code/OptionalStoppingAlt.lean`
(`optional_stopping_alt_ui_preserved`) has two unproved bounds.
The bounded-stopping-time conditional form was formalized separately.
This file proves expectation preservation and UI preservation for
*martingales*; the full submartingale cases are omitted.

## Proof outline

For a uniformly integrable martingale, Mathlib's `L¹` martingale
convergence theorem writes `f n =ᵐ[μ] μ[f_∞ | ℱ n]`. Optional sampling
at the bounded stopping time `τ ∧ n` then gives
`f_{τ ∧ n} =ᵐ[μ] μ[f n | ℱ_{τ ∧ n}]`, and the tower property of
conditional expectation collapses the right-hand side to
`μ[f_∞ | ℱ_{τ ∧ n}]`. Hence the stopped process is a family of
conditional expectations of the single integrable function `f_∞`,
so it is uniformly integrable (Mathlib), and Vitali's theorem gives
`L¹` convergence of `f_{τ ∧ n}` to `f_τ`. The expectation equalities
follow because every `∫ f_{τ ∧ n}` equals `∫ f 0` by bounded optional
stopping and every `∫ f n` equals `∫ f_∞`.

## Main results

* `MeasureTheory.Martingale.uniformIntegrable_stoppedProcess_of_uniformIntegrable`:
  stopping a uniformly integrable martingale at an arbitrary stopping
  time yields a uniformly integrable stopped process.
* `MeasureTheory.Martingale.integral_stoppedValueAtTop_eq_of_uniformIntegrable`:
  `∫ f 0 = ∫ f_τ = ∫ f_∞` for a uniformly integrable martingale `f`
  and an arbitrary stopping time `τ`.
-/

@[expose] public section

open scoped MeasureTheory NNReal ENNReal Topology
open MeasureTheory Filter

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- The value of a process `f` at a possibly infinite stopping time `τ`:
`f (τ ω) ω` when `τ ω < ∞`, and the limit `limUnder atTop (f · ω)` when
`τ ω = ∞`. This extends `stoppedValue` (which uses an arbitrary finite index at `τ = ⊤`)
to allow infinite stopping times, as required for the general optional
stopping theorem. -/
noncomputable def stoppedValueAtTop (f : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) : Ω → ℝ :=
  fun ω => if τ ω = ⊤ then Filter.limUnder atTop (fun n => f n ω) else f (τ ω).untopA ω

/-- The stopped process at the bounded stopping time `τ ∧ n` is the
conditional expectation of the martingale's limit process with respect
to the stopped σ-algebra `ℱ_{τ ∧ n}`. This is optional sampling
combined with the tower property. -/
private theorem stoppedProcess_ae_eq_condExp_limitProcess
    (hmart : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    stoppedProcess f τ n =ᵐ[μ]
      μ[ℱ.limitProcess f μ |
        (IsStoppingTime.min (isStoppingTime_const ℱ (n : ℕ)) hτ).measurableSpace] := by
  have hσ : IsStoppingTime ℱ (fun ω => min (↑n : WithTop ℕ) (τ ω)) :=
    (isStoppingTime_const ℱ n).min hτ
  rw [stoppedProcess_eq_stoppedValue]
  have h1 : stoppedValue f (fun ω => min (↑n : WithTop ℕ) (τ ω)) =ᵐ[μ]
      μ[f n | hσ.measurableSpace] := by
    have h := hmart.stoppedValue_ae_eq_condExp_of_le (isStoppingTime_const ℱ n) hσ
      (fun ω => min_le_left _ _) (fun ω => le_rfl)
    rwa [stoppedValue_const] at h
  refine h1.trans ?_
  have h3 : μ[f n | hσ.measurableSpace] =ᵐ[μ]
      μ[μ[ℱ.limitProcess f μ | ℱ n] | hσ.measurableSpace] :=
    condExp_congr_ae (hmart.ae_eq_condExp_limitProcess hui n)
  refine h3.trans ?_
  exact condExp_condExp_of_le (hσ.measurableSpace_le_of_le_const (fun ω => min_le_left _ _))
    (ℱ.le n)

/-- Stopping a uniformly integrable martingale at an arbitrary stopping
time yields a uniformly integrable stopped process. The stopped process
is a family of conditional expectations of the single integrable limit
process, hence uniformly integrable. -/
theorem Martingale.uniformIntegrable_stoppedProcess_of_uniformIntegrable
    (hmart : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    UniformIntegrable (stoppedProcess f τ) 1 μ := by
  obtain ⟨R, hR⟩ := hui.2
  have hg_int : Integrable (ℱ.limitProcess f μ) μ :=
    (Filtration.memLp_limitProcess_of_eLpNorm_bdd hui.aestronglyMeasurable hR).integrable le_rfl
  have hcond : UniformIntegrable (fun n => μ[ℱ.limitProcess f μ |
      (IsStoppingTime.min (isStoppingTime_const ℱ (n : ℕ)) hτ).measurableSpace]) 1 μ :=
    hg_int.uniformIntegrable_condExp
      (fun n => ((isStoppingTime_const ℱ n).min hτ).measurableSpace_le)
  exact hcond.ae_eq (fun n => (stoppedProcess_ae_eq_condExp_limitProcess hmart hui τ hτ n).symm)

/-- **General optional stopping for uniformly integrable martingales.**
If `f` is a uniformly integrable martingale and `τ` is any stopping
time (possibly infinite), then the expectation at the stopping time
equals the initial expectation and the expectation of the limit:
`∫ f 0 = ∫ f_τ = ∫ f_∞`. -/
theorem Martingale.integral_stoppedValueAtTop_eq_of_uniformIntegrable
    (hmart : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    (∫ ω, f 0 ω ∂μ = ∫ ω, stoppedValueAtTop f τ ω ∂μ) ∧
    (∫ ω, stoppedValueAtTop f τ ω ∂μ = ∫ ω, ℱ.limitProcess f μ ω ∂μ) := by
  obtain ⟨R, hR⟩ := hui.2
  have hg_int : Integrable (ℱ.limitProcess f μ) μ :=
    (Filtration.memLp_limitProcess_of_eLpNorm_bdd hui.aestronglyMeasurable hR).integrable le_rfl
  have hUIstop : UniformIntegrable (stoppedProcess f τ) 1 μ :=
    hmart.uniformIntegrable_stoppedProcess_of_uniformIntegrable hui τ hτ
  -- The stopped process converges a.e. to the stopped value at `τ`.
  have hae_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop
      (𝓝 (ℱ.limitProcess f μ ω)) :=
    hmart.submartingale.ae_tendsto_limitProcess hR
  have hae_stop : ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedProcess f τ n ω) atTop
      (𝓝 (stoppedValueAtTop f τ ω)) := by
    filter_upwards [hae_lim] with ω hω
    by_cases hτfin : τ ω = ⊤
    · have hstop : ∀ n, stoppedProcess f τ n ω = f n ω := by
        intro n
        simp only [stoppedProcess]
        rw [hτfin, min_top_right]
        rfl
      have hval : stoppedValueAtTop f τ ω = ℱ.limitProcess f μ ω := by
        simp only [stoppedValueAtTop, hτfin, ite_true]
        exact hω.limUnder_eq
      rw [hval]
      exact hω.congr (fun n => (hstop n).symm)
    · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hτfin
      have hstop_ev : ∀ᶠ n in atTop, stoppedProcess f τ n ω = f k ω := by
        filter_upwards [eventually_ge_atTop k] with n hn
        have hge : τ ω ≤ (↑n : WithTop ℕ) := by
          rw [← hk]
          exact WithTop.coe_le_coe.mpr hn
        calc stoppedProcess f τ n ω = f (τ ω).untopA ω :=
              stoppedProcess_eq_of_ge hge
          _ = f k ω := by
              rw [← hk]
              rfl
      have hval : stoppedValueAtTop f τ ω = f k ω := by
        simp only [stoppedValueAtTop, hτfin, ite_false]
        rw [← hk]
        rfl
      rw [hval]
      exact tendsto_const_nhds.congr' (hstop_ev.mono fun n hn => hn.symm)
  -- Every stopped expectation equals the initial expectation, by
  -- bounded optional stopping applied to `f` and to `-f`.
  have hInt_stop : ∀ n, ∫ ω, stoppedProcess f τ n ω ∂μ = ∫ ω, f 0 ω ∂μ := by
    intro n
    have hσ : IsStoppingTime ℱ (fun ω => min (↑n : WithTop ℕ) (τ ω)) :=
      (isStoppingTime_const ℱ n).min hτ
    have hstop_eq : stoppedProcess f τ n = stoppedValue f (fun ω => min (↑n : WithTop ℕ) (τ ω)) := by
      funext ω
      rfl
    rw [hstop_eq]
    have hle : (∫ ω, stoppedValue f (fun _ : Ω => ((0 : ℕ) : WithTop ℕ)) ω ∂μ) ≤
        ∫ ω, stoppedValue f (fun ω => min (↑n : WithTop ℕ) (τ ω)) ω ∂μ := by
      apply hmart.submartingale.expected_stoppedValue_mono
        (isStoppingTime_const ℱ 0) hσ (fun ω => bot_le)
        (fun ω => min_le_left _ _)
    have hge : (∫ ω, stoppedValue f (fun ω => min (↑n : WithTop ℕ) (τ ω)) ω ∂μ) ≤
        ∫ ω, stoppedValue f (fun _ : Ω => ((0 : ℕ) : WithTop ℕ)) ω ∂μ := by
      have h := hmart.neg.submartingale.expected_stoppedValue_mono
        (isStoppingTime_const ℱ 0) hσ (fun ω => bot_le) (fun ω => min_le_left _ _)
      simp only [stoppedValue_neg, Pi.neg_apply, integral_neg] at h
      exact neg_le_neg_iff.mp h
    have hconst : ∫ ω, stoppedValue f (fun _ : Ω => ((0 : ℕ) : WithTop ℕ)) ω ∂μ = ∫ ω, f 0 ω ∂μ := by
      congr 1
    rw [hconst] at hle hge
    exact le_antisymm hge hle
  -- `L¹` convergence of the stopped process to the stopped value.
  have hL1 : Tendsto (fun n => eLpNorm (stoppedProcess f τ n - stoppedValueAtTop f τ) 1 μ)
      atTop (𝓝 0) := by
    refine tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
      hUIstop.aestronglyMeasurable (hUIstop.memLp_of_ae_tendsto hae_stop) hUIstop.1 ?_
    exact tendstoInMeasure_of_tendsto_ae hUIstop.aestronglyMeasurable hae_stop
  have hIntTendsto : Tendsto (fun n => ∫ ω, stoppedProcess f τ n ω ∂μ) atTop
      (𝓝 (∫ ω, stoppedValueAtTop f τ ω ∂μ)) := by
    refine tendsto_integral_of_L1' (stoppedValueAtTop f τ)
      (Filter.Eventually.of_forall fun n => (hUIstop.memLp n).integrable le_rfl) hL1
  have hInt_eq0 : ∫ ω, stoppedValueAtTop f τ ω ∂μ = ∫ ω, f 0 ω ∂μ := by
    have hseq : (fun n : ℕ => ∫ ω, stoppedProcess f τ n ω ∂μ) =
        fun _ : ℕ => ∫ ω, f 0 ω ∂μ := funext hInt_stop
    have hconst_seq : Tendsto (fun _ : ℕ => ∫ ω, f 0 ω ∂μ) atTop
        (𝓝 (∫ ω, stoppedValueAtTop f τ ω ∂μ)) := by
      simpa [hseq] using hIntTendsto
    exact tendsto_nhds_unique hconst_seq tendsto_const_nhds
  have hInt0 : ∫ ω, f 0 ω ∂μ = ∫ ω, ℱ.limitProcess f μ ω ∂μ := by
    have h := hmart.ae_eq_condExp_limitProcess hui 0
    rw [integral_congr_ae h]
    exact integral_condExp (ℱ.le 0)
  constructor
  · exact hInt_eq0.symm
  · exact hInt_eq0.trans hInt0

end MeasureTheory
