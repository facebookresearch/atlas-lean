/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OptionalStoppingUniformIntegrable
import Mathlib.Probability.Martingale.Centering

/-!
# Optional stopping for uniformly integrable submartingales

For a uniformly integrable submartingale `f` and an *arbitrary* stopping
time `τ` (possibly infinite), stopping preserves uniform integrability,
and the stopped expectation is squeezed between the initial expectation
and the expectation of the limit:
`∫ f 0 ≤ ∫ f_τ ≤ ∫ f_∞`, where `f_∞` is the a.e. limit of `f` and `f_τ`
is `f` evaluated at `τ`, with the limit `f_∞` used on `{τ = ∞}`.

## Source

This formalizes the targets "Theorem (General optional stopping,
uniform integrability preservation)" and "Theorem (General optional
stopping, expectation inequality)" (Lecture 29) of
`v1/Atlas/TheoryOfProbability/targets.yaml`:

* "Let `X_n` be a uniformly integrable submartingale. For any stopping
  time `N`, `X_{N ∧ n}` is uniformly integrable."
* "Let `X_n` be a uniformly integrable submartingale. For any stopping
  time `N ≤ ∞`, we have `EX_0 ≤ EX_N ≤ EX_∞` where `X_∞ = lim X_n`."

The v1 formalizations are
`v1/Atlas/TheoryOfProbability/code/OptionalStoppingAlt.lean`
(`optional_stopping_alt_ui_preserved`, with two unproved bounds) and
`v1/Atlas/TheoryOfProbability/code/GeneralOptionalStopping.lean`
(`general_optional_stopping`, left unproved). The bounded-stopping-time
conditional form was ported in an earlier batch (bounded optional
stopping); the martingale form of the unbounded theorem was ported in an
earlier batch (optional stopping for uniformly integrable martingales);
this file is the submartingale form, whose uniform-integrability
preservation was the hard step left open in v1.

## Proof outline

Write `f = M + A` for the Doob decomposition of `f`: `M` is a
martingale (`martingalePart`) and `A` is a predictable, a.e. monotone,
a.e. nonnegative process (`predictablePart`) with `A 0 = 0`. Since `f`
is uniformly integrable, so is `A`: its expectations `∫ A_n` are
uniformly bounded (they equal `∫ f_n - ∫ f_0`), so its a.e. supremum
`A_∞` is integrable and dominates every `A_n` a.e. Then `M = f - A`
is uniformly integrable as a difference of uniformly integrable
families. Stopping the martingale part preserves uniform integrability
by the martingale argument (optional sampling at `τ ∧ n` writes the
stopped process as conditional expectations of the single integrable
limit process), and stopping the predictable part preserves it by
domination by `A_∞`. Summing gives uniform integrability of the stopped
submartingale. The expectation inequality follows from bounded optional
stopping applied to `τ ∧ n` and `n`, passing to the limit using `L¹`
convergence of the stopped process (Vitali) and of `f_n` to `f_∞`.

## Notes on scope

The value at a possibly infinite stopping time, `stoppedValueAtTop`, and
martingale uniform-integrability preservation are supplied by
`MathlibExt.Probability.OptionalStoppingUniformIntegrable`. This file
proves the predictable-part estimates, combines them with the existing
martingale theorem, and derives the submartingale expectation bounds.
The conditional form of general optional stopping
(`Y_L ≤ E[Y_M | ℱ_L]` for stopping times `L ≤ M`) is not claimed here.

## Main results

* `MeasureTheory.Submartingale.uniformIntegrable_stoppedProcess_of_uniformIntegrable`:
  stopping a uniformly integrable submartingale at an arbitrary stopping
  time yields a uniformly integrable stopped process.
* `MeasureTheory.Submartingale.integral_stoppedValueAtTop_of_uniformIntegrable`:
  `∫ f 0 ≤ ∫ f_τ ≤ ∫ f_∞` for a uniformly integrable submartingale `f`
  and an arbitrary stopping time `τ`.
-/

@[expose] public section

open scoped MeasureTheory NNReal ENNReal Topology
open MeasureTheory Filter

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- The a.e.-finite supremum of the predictable part of `f`, as a
real-valued function: `sup_n A_n`, where `A` is the predictable part in
Doob's decomposition. -/
private noncomputable def predictablePartSup (f : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) : Ω → ℝ :=
  fun ω => (⨆ n, ENNReal.ofReal (predictablePart f ℱ μ n ω)).toReal

omit [IsProbabilityMeasure μ] in
/-- Every term of the predictable part is measurable. -/
private theorem measurable_predictablePart (n : ℕ) :
    Measurable (predictablePart f ℱ μ n) :=
  ((stronglyAdapted_predictablePart' (f := f) (ℱ := ℱ) (μ := μ) n).mono (ℱ.le n)).measurable

omit [IsProbabilityMeasure μ] in
/-- The a.e.-finite supremum of the predictable part is measurable. -/
private theorem measurable_predictablePartSup :
    Measurable (predictablePartSup f ℱ μ) := by
  unfold predictablePartSup
  exact (Measurable.iSup
    (fun n => (measurable_predictablePart (f := f) (ℱ := ℱ) (μ := μ) n).ennreal_ofReal)).ennreal_toReal

omit [IsProbabilityMeasure μ] in
/-- The a.e.-finite supremum of the predictable part is nonnegative. -/
private theorem predictablePartSup_nonneg (ω : Ω) : 0 ≤ predictablePartSup f ℱ μ ω :=
  ENNReal.toReal_nonneg

omit [IsProbabilityMeasure μ] in
/-- An integral is bounded by its `L¹` norm. -/
private theorem integral_le_eLpNorm_one {g : Ω → ℝ} (hg : Integrable g μ)
    (C : ℝ≥0) (hC : eLpNorm g 1 μ ≤ C) : ∫ ω, g ω ∂μ ≤ (C : ℝ) := by
  calc ∫ ω, g ω ∂μ ≤ ∫ ω, ‖g ω‖ ∂μ := integral_mono_ae hg hg.norm
        (ae_of_all _ (fun _ => le_abs_self _))
    _ = (eLpNorm g 1 μ).toReal := by
        rw [integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable,
          eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable]
    _ ≤ (C : ℝ) := ENNReal.toReal_mono (by simp) hC

/-- The expectation of each term of the predictable part is uniformly
bounded: `∫ A_n = ∫ f_n - ∫ f_0`, and both terms are bounded by the `L¹`
bound from uniform integrability. -/
private theorem integral_predictablePart_le (hsub : Submartingale f ℱ μ) {C : ℝ≥0}
    (hC : ∀ i, eLpNorm (f i) 1 μ ≤ (C : ℝ≥0∞)) (n : ℕ) :
    ∫ ω, predictablePart f ℱ μ n ω ∂μ ≤ 2 * (C : ℝ) := by
  have hmart : Martingale (martingalePart f ℱ μ) ℱ μ :=
    martingale_martingalePart hsub.stronglyAdapted (fun k => hsub.integrable k)
  have hM_int : ∀ k, ∫ ω, martingalePart f ℱ μ k ω ∂μ = ∫ ω, f 0 ω ∂μ := by
    intro k
    have hcond : (μ[martingalePart f ℱ μ k | ℱ 0]) =ᵐ[μ] martingalePart f ℱ μ 0 :=
      hmart.condExp_ae_eq (Nat.zero_le k)
    have h : ∫ ω, (μ[martingalePart f ℱ μ k | ℱ 0]) ω ∂μ =
        ∫ ω, martingalePart f ℱ μ k ω ∂μ := integral_condExp (ℱ.le 0)
    rw [integral_congr_ae hcond] at h
    rw [← h, martingalePart_zero]
  have hA_eq : ∫ ω, predictablePart f ℱ μ n ω ∂μ =
      ∫ ω, f n ω ∂μ - ∫ ω, f 0 ω ∂μ := by
    have hdecomp : ∀ ω, predictablePart f ℱ μ n ω =
        f n ω - martingalePart f ℱ μ n ω := by
      intro ω
      have hω := congrFun (congrFun (martingalePart_add_predictablePart ℱ μ f) n) ω
      simp only [Pi.add_apply] at hω
      linarith
    rw [integral_congr_ae (Filter.Eventually.of_forall hdecomp),
      integral_sub (hsub.integrable n)
        (integrable_martingalePart (fun k => hsub.integrable k) n), hM_int n]
  rw [hA_eq]
  have hf_le : ∫ ω, f n ω ∂μ ≤ (C : ℝ) :=
    integral_le_eLpNorm_one (hsub.integrable n) C (hC n)
  have hf0_ge : -((C : ℝ)) ≤ ∫ ω, f 0 ω ∂μ := by
    have habs : |∫ ω, f 0 ω ∂μ| ≤ (C : ℝ) := by
      rw [← Real.norm_eq_abs]
      calc ‖∫ ω, f 0 ω ∂μ‖ ≤ ∫ ω, ‖f 0 ω‖ ∂μ := norm_integral_le_integral_norm _
        _ = (eLpNorm (f 0) 1 μ).toReal := by
            rw [integral_norm_eq_lintegral_enorm (hsub.integrable 0).aestronglyMeasurable,
              eLpNorm_one_eq_lintegral_enorm (hsub.integrable 0).aestronglyMeasurable]
        _ ≤ (C : ℝ) := ENNReal.toReal_mono (by simp) (hC 0)
    linarith [abs_le.mp habs]
  linarith

/-- The supremum of the predictable part is integrable, and it dominates
every term of the predictable part a.e. This is the key estimate: the
predictable part of a uniformly integrable submartingale is itself
uniformly integrable, because it is dominated by its integrable
supremum. -/
private theorem predictablePartSup_spec (hsub : Submartingale f ℱ μ) {C : ℝ≥0}
    (hC : ∀ i, eLpNorm (f i) 1 μ ≤ (C : ℝ≥0∞)) :
    MemLp (predictablePartSup f ℱ μ) 1 μ ∧
      (∀ᵐ ω ∂μ, ∀ n, predictablePart f ℱ μ n ω ≤ predictablePartSup f ℱ μ ω) ∧
      eLpNorm (predictablePartSup f ℱ μ) 1 μ ≤ ENNReal.ofReal (2 * (C : ℝ)) := by
  have hA_int : ∀ n, Integrable (predictablePart f ℱ μ n) μ := by
    intro n
    have hA_eq_fun : predictablePart f ℱ μ n = f n - martingalePart f ℱ μ n := by
      funext ω
      have hω := congrFun (congrFun (martingalePart_add_predictablePart ℱ μ f) n) ω
      simp only [Pi.add_apply, Pi.sub_apply] at hω ⊢
      linarith
    rw [hA_eq_fun]
    exact (hsub.integrable n).sub (integrable_martingalePart (fun k => hsub.integrable k) n)
  have hmono : ∀ᵐ ω ∂μ, Monotone (fun n => ENNReal.ofReal (predictablePart f ℱ μ n ω)) := by
    filter_upwards [hsub.monotone_predictablePart] with ω hω i j hij
    exact ENNReal.ofReal_le_ofReal (hω hij)
  have hlin : ∫⁻ ω, ⨆ n, ENNReal.ofReal (predictablePart f ℱ μ n ω) ∂μ ≤
      ENNReal.ofReal (2 * (C : ℝ)) := by
    rw [lintegral_iSup' (fun n =>
      (measurable_predictablePart (f := f) (ℱ := ℱ) (μ := μ) n).ennreal_ofReal.aemeasurable) hmono]
    refine iSup_le fun n => ?_
    have hInt : ∫⁻ ω, ENNReal.ofReal (predictablePart f ℱ μ n ω) ∂μ =
        ENNReal.ofReal (∫ ω, predictablePart f ℱ μ n ω ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hA_int n)
        (hsub.predictablePart_nonneg.mono fun ω hω => hω n)]
    rw [hInt]
    exact ENNReal.ofReal_le_ofReal (integral_predictablePart_le hsub hC n)
  have hfin : ∀ᵐ ω ∂μ, (⨆ n, ENNReal.ofReal (predictablePart f ℱ μ n ω)) ≠ ⊤ := by
    have hne : (∫⁻ ω, ⨆ n, ENNReal.ofReal (predictablePart f ℱ μ n ω) ∂μ) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
    filter_upwards [ae_lt_top
      (Measurable.iSup (fun n =>
        (measurable_predictablePart (f := f) (ℱ := ℱ) (μ := μ) n).ennreal_ofReal)) hne]
      with ω hω
    exact hω.ne
  have hle : ∀ᵐ ω ∂μ, ∀ n, predictablePart f ℱ μ n ω ≤ predictablePartSup f ℱ μ ω := by
    filter_upwards [hsub.predictablePart_nonneg, hfin] with ω hω hfinω n
    calc predictablePart f ℱ μ n ω
        = (ENNReal.ofReal (predictablePart f ℱ μ n ω)).toReal := by
          rw [ENNReal.toReal_ofReal (hω n)]
      _ ≤ (⨆ m, ENNReal.ofReal (predictablePart f ℱ μ m ω)).toReal :=
          ENNReal.toReal_mono hfinω (le_iSup (fun m => ENNReal.ofReal (predictablePart f ℱ μ m ω)) n)
      _ = predictablePartSup f ℱ μ ω := rfl
  have heLpNormLe : eLpNorm (predictablePartSup f ℱ μ) 1 μ ≤ ENNReal.ofReal (2 * (C : ℝ)) := by
    rw [eLpNorm_one_eq_lintegral_enorm measurable_predictablePartSup.aestronglyMeasurable]
    have hEq : ∫⁻ ω, ‖predictablePartSup f ℱ μ ω‖ₑ ∂μ =
        ∫⁻ ω, ⨆ n, ENNReal.ofReal (predictablePart f ℱ μ n ω) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hfin] with ω hfinω
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (predictablePartSup_nonneg (f := f) (ℱ := ℱ) (μ := μ) ω)]
      show ENNReal.ofReal ((⨆ n, ENNReal.ofReal (predictablePart f ℱ μ n ω)).toReal) =
        ⨆ n, ENNReal.ofReal (predictablePart f ℱ μ n ω)
      rw [ENNReal.ofReal_toReal hfinω]
    rw [hEq]
    exact hlin
  have hMemLp : MemLp (predictablePartSup f ℱ μ) 1 μ :=
    lt_of_le_of_lt heLpNormLe ENNReal.ofReal_lt_top
  exact ⟨hMemLp, hle, heLpNormLe⟩

/-- The predictable part of a uniformly integrable submartingale is
uniformly integrable. -/
private theorem uniformIntegrable_predictablePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) : UniformIntegrable (predictablePart f ℱ μ) 1 μ := by
  obtain ⟨_, ⟨C, hC⟩⟩ := hui
  obtain ⟨hMemLp, hle, -⟩ := predictablePartSup_spec hsub hC
  have hae : ∀ n, AEStronglyMeasurable (predictablePart f ℱ μ n) μ := fun n =>
    ((stronglyAdapted_predictablePart' (f := f) (ℱ := ℱ) (μ := μ) n).mono (ℱ.le n)).aestronglyMeasurable
  have hBound : ∀ n, eLpNorm (predictablePart f ℱ μ n) 1 μ ≤
      ((Real.toNNReal (2 * (C : ℝ)) : ℝ≥0) : ℝ≥0∞) := by
    intro n
    have hA_int : Integrable (predictablePart f ℱ μ n) μ := by
      have hA_eq_fun : predictablePart f ℱ μ n = f n - martingalePart f ℱ μ n := by
        funext ω
        have hω := congrFun (congrFun (martingalePart_add_predictablePart ℱ μ f) n) ω
        simp only [Pi.add_apply, Pi.sub_apply] at hω ⊢
        linarith
      rw [hA_eq_fun]
      exact (hsub.integrable n).sub (integrable_martingalePart (fun k => hsub.integrable k) n)
    rw [eLpNorm_one_eq_lintegral_enorm (hae n)]
    have hEq : ∫⁻ ω, ‖predictablePart f ℱ μ n ω‖ₑ ∂μ =
        ∫⁻ ω, ENNReal.ofReal (predictablePart f ℱ μ n ω) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hsub.predictablePart_nonneg] with ω hω
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hω n)]
    rw [hEq, ← ofReal_integral_eq_lintegral_ofReal (hA_int)
      (hsub.predictablePart_nonneg.mono fun ω hω => hω n)]
    exact ENNReal.ofReal_le_ofReal (integral_predictablePart_le hsub hC n)
  refine ⟨UnifIntegrable.ae_mono (unifIntegrable_const le_rfl ENNReal.one_ne_top hMemLp) hae
      (fun n => ?_), Real.toNNReal (2 * (C : ℝ)), fun n => hBound n⟩
  · filter_upwards [hsub.predictablePart_nonneg, hle] with ω hω hleω
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hω n), Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (predictablePartSup_nonneg (f := f) (ℱ := ℱ) (μ := μ) ω)]
    exact ENNReal.ofReal_le_ofReal (hleω n)

/-- The martingale part of a uniformly integrable submartingale is
uniformly integrable, as the difference of two uniformly integrable
families. -/
private theorem uniformIntegrable_martingalePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) : UniformIntegrable (martingalePart f ℱ μ) 1 μ := by
  have hA_UI := uniformIntegrable_predictablePart hsub hui
  obtain ⟨h1, ⟨Cf, hCf⟩⟩ := hui
  obtain ⟨hA1, ⟨CA, hCA⟩⟩ := hA_UI
  have hsub_UI : UniformIntegrable (f - predictablePart f ℱ μ) 1 μ := by
    refine ⟨h1.sub hA1 le_rfl, ⟨Cf + CA, fun n => ?_⟩⟩
    calc eLpNorm ((f - predictablePart f ℱ μ) n) 1 μ
        = eLpNorm (f n - predictablePart f ℱ μ n) 1 μ := rfl
      _ ≤ eLpNorm (f n) 1 μ + eLpNorm (predictablePart f ℱ μ n) 1 μ :=
          eLpNorm_sub_le le_rfl
      _ ≤ (Cf : ℝ≥0∞) + (CA : ℝ≥0∞) := add_le_add (hCf n) (hCA n)
  exact hsub_UI.ae_eq (fun n => Filter.EventuallyEq.of_eq rfl)

/-- The stopped predictable part is uniformly integrable, by domination
by the integrable supremum of the predictable part. -/
private theorem uniformIntegrable_stoppedProcess_predictablePart
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    UniformIntegrable (stoppedProcess (predictablePart f ℱ μ) τ) 1 μ := by
  obtain ⟨_, ⟨C, hC⟩⟩ := hui
  obtain ⟨hMemLp, hle, hSupLe⟩ := predictablePartSup_spec hsub hC
  have hae : ∀ n, AEStronglyMeasurable (stoppedProcess (predictablePart f ℱ μ) τ n) μ :=
    fun n => ((stronglyAdapted_predictablePart' (f := f) (ℱ := ℱ) (μ := μ)).stronglyMeasurable_stoppedProcess_of_discrete hτ n).aestronglyMeasurable
  refine ⟨UnifIntegrable.ae_mono (unifIntegrable_const le_rfl ENNReal.one_ne_top hMemLp) hae
      (fun n => ?_), Real.toNNReal (2 * (C : ℝ)), fun n => ?_⟩
  · filter_upwards [hsub.predictablePart_nonneg, hle] with ω hω hleω
    have hstop : stoppedProcess (predictablePart f ℱ μ) τ n ω =
        predictablePart f ℱ μ (min (↑n : WithTop ℕ) (τ ω)).untopA ω := rfl
    rw [hstop, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hω _), Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (predictablePartSup_nonneg (f := f) (ℱ := ℱ) (μ := μ) ω)]
    exact ENNReal.ofReal_le_ofReal (hleω _)
  · calc eLpNorm (stoppedProcess (predictablePart f ℱ μ) τ n) 1 μ
        ≤ eLpNorm (predictablePartSup f ℱ μ) 1 μ := by
          refine eLpNorm_mono_ae (hae n) ?_
          filter_upwards [hsub.predictablePart_nonneg, hle] with ω hω hleω
          have hstop : stoppedProcess (predictablePart f ℱ μ) τ n ω =
              predictablePart f ℱ μ (min (↑n : WithTop ℕ) (τ ω)).untopA ω := rfl
          rw [hstop, Real.norm_eq_abs, abs_of_nonneg (hω _), Real.norm_eq_abs,
            abs_of_nonneg (predictablePartSup_nonneg (f := f) (ℱ := ℱ) (μ := μ) ω)]
          exact hleω _
      _ ≤ ENNReal.ofReal (2 * (C : ℝ)) := hSupLe
      _ = ((Real.toNNReal (2 * (C : ℝ)) : ℝ≥0) : ℝ≥0∞) := rfl

/-- **General optional stopping, uniform integrability preservation.** Let $\mu$ be a
probability measure and let $(f_n)_{n \in \mathbb{N}}$ be a real-valued submartingale with
respect to a filtration $(\mathcal{F}_n)_{n \in \mathbb{N}}$ that is uniformly integrable. Then
for every stopping time $\tau$ with values in $\mathbb{N} \cup \{\infty\}$, the stopped process
$(f_{\tau \wedge n})_{n \in \mathbb{N}}$ is uniformly integrable. -/
theorem Submartingale.uniformIntegrable_stoppedProcess_of_uniformIntegrable
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    UniformIntegrable (stoppedProcess f τ) 1 μ := by
  have hMmart : Martingale (martingalePart f ℱ μ) ℱ μ :=
    martingale_martingalePart hsub.stronglyAdapted (fun k => hsub.integrable k)
  have hM_UI := uniformIntegrable_martingalePart hsub hui
  have hA_UI := uniformIntegrable_stoppedProcess_predictablePart hsub hui τ hτ
  have hMstop_UI :=
    hMmart.uniformIntegrable_stoppedProcess_of_uniformIntegrable hM_UI τ hτ
  have hdecomp : stoppedProcess f τ =
      stoppedProcess (martingalePart f ℱ μ) τ + stoppedProcess (predictablePart f ℱ μ) τ := by
    funext n ω
    have h := congrFun (martingalePart_add_predictablePart ℱ μ f)
      (min (↑n : WithTop ℕ) (τ ω)).untopA
    have h' := congrFun h ω
    simp only [Pi.add_apply] at h'
    simp only [stoppedProcess, Pi.add_apply]
    exact h'.symm
  rw [hdecomp]
  obtain ⟨hM1, ⟨CM, hCM⟩⟩ := hMstop_UI
  obtain ⟨hA1, ⟨CA, hCA⟩⟩ := hA_UI
  refine ⟨hM1.add hA1 le_rfl, ⟨CM + CA, fun n => ?_⟩⟩
  calc eLpNorm ((stoppedProcess (martingalePart f ℱ μ) τ +
        stoppedProcess (predictablePart f ℱ μ) τ) n) 1 μ
      = eLpNorm (stoppedProcess (martingalePart f ℱ μ) τ n +
          stoppedProcess (predictablePart f ℱ μ) τ n) 1 μ := rfl
    _ ≤ eLpNorm (stoppedProcess (martingalePart f ℱ μ) τ n) 1 μ +
          eLpNorm (stoppedProcess (predictablePart f ℱ μ) τ n) 1 μ := eLpNorm_add_le le_rfl
    _ ≤ (CM : ℝ≥0∞) + (CA : ℝ≥0∞) := add_le_add (hCM n) (hCA n)

/-- **General optional stopping, expectation inequality.** Let $\mu$ be a probability measure,
let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration and let $(f_n)_{n \in \mathbb{N}}$ be a
real-valued submartingale with respect to $(\mathcal{F}_n)$ that is uniformly integrable. Let
$f_\infty$ be the limit process of $f$ (its almost-everywhere limit, by the martingale
convergence theorem). Then for every stopping time $\tau$ with values in
$\mathbb{N} \cup \{\infty\}$, the value $f_\tau$ of $f$ at $\tau$ (at points where
$\tau = \infty$ it is $\lim_n f_n$) satisfies
$\int f_0 \, d\mu \le \int f_\tau \, d\mu \le \int f_\infty \, d\mu$. -/
theorem Submartingale.integral_stoppedValueAtTop_of_uniformIntegrable
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    (∫ ω, f 0 ω ∂μ ≤ ∫ ω, stoppedValueAtTop f τ ω ∂μ) ∧
    (∫ ω, stoppedValueAtTop f τ ω ∂μ ≤ ∫ ω, ℱ.limitProcess f μ ω ∂μ) := by
  obtain ⟨R, hR⟩ := hui.2
  have hUIstop : UniformIntegrable (stoppedProcess f τ) 1 μ :=
    hsub.uniformIntegrable_stoppedProcess_of_uniformIntegrable hui τ hτ
  have hae_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) :=
    hsub.ae_tendsto_limitProcess hR
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
        calc stoppedProcess f τ n ω = f (τ ω).untopA ω := stoppedProcess_eq_of_ge hge
          _ = f k ω := by
              rw [← hk]
              rfl
      have hval : stoppedValueAtTop f τ ω = f k ω := by
        simp only [stoppedValueAtTop, hτfin, ite_false]
        rw [← hk]
        rfl
      rw [hval]
      exact tendsto_const_nhds.congr' (hstop_ev.mono fun n hn => hn.symm)
  have hL1 : Tendsto (fun n => eLpNorm (stoppedProcess f τ n - stoppedValueAtTop f τ) 1 μ)
      atTop (𝓝 0) := by
    refine tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
      hUIstop.aestronglyMeasurable (hUIstop.memLp_of_ae_tendsto hae_stop) hUIstop.1 ?_
    exact tendstoInMeasure_of_tendsto_ae hUIstop.aestronglyMeasurable hae_stop
  have hIntTendsto : Tendsto (fun n => ∫ ω, stoppedProcess f τ n ω ∂μ) atTop
      (𝓝 (∫ ω, stoppedValueAtTop f τ ω ∂μ)) := by
    refine tendsto_integral_of_L1' (stoppedValueAtTop f τ)
      (Filter.Eventually.of_forall fun n => (hUIstop.memLp n).integrable le_rfl) hL1
  have hInt_f : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop
      (𝓝 (∫ ω, ℱ.limitProcess f μ ω ∂μ)) := by
    refine tendsto_integral_of_L1' (ℱ.limitProcess f μ)
      (Filter.Eventually.of_forall fun n => hsub.integrable n) ?_
    exact hsub.tendsto_eLpNorm_one_limitProcess hui
  have hle0 : ∀ n, ∫ ω, f 0 ω ∂μ ≤ ∫ ω, stoppedProcess f τ n ω ∂μ := by
    intro n
    have hσ : IsStoppingTime ℱ (fun ω => min (↑n : WithTop ℕ) (τ ω)) :=
      (isStoppingTime_const ℱ n).min hτ
    have h := hsub.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hσ
      (fun ω => bot_le) (fun ω => min_le_left _ _)
    rwa [stoppedValue_const] at h
  have hleN : ∀ n, ∫ ω, stoppedProcess f τ n ω ∂μ ≤ ∫ ω, f n ω ∂μ := by
    intro n
    have hσ : IsStoppingTime ℱ (fun ω => min (↑n : WithTop ℕ) (τ ω)) :=
      (isStoppingTime_const ℱ n).min hτ
    have h := hsub.expected_stoppedValue_mono hσ (isStoppingTime_const ℱ n)
      (fun ω => min_le_left _ _) (fun ω => le_rfl)
    rwa [stoppedValue_const] at h
  constructor
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hIntTendsto
      (Filter.Eventually.of_forall hle0)
  · exact le_of_tendsto_of_tendsto hIntTendsto hInt_f (Filter.Eventually.of_forall hleN)

end MeasureTheory
